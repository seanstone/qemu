/*
 * linux fbdev output driver.
 *
 * Author: Gerd Hoffmann <address@hidden>
 *
 * This work is licensed under the terms of the GNU GPL, version 2 or later.
 * See the COPYING file in the top-level directory.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <termios.h>

#include <sys/ioctl.h>
#include <sys/mman.h>

#include <linux/kd.h>
#include <linux/vt.h>
#include <linux/fb.h>

#include "qemu/osdep.h"
#include "qemu-common.h"
#include "qemu/cutils.h"
#include "keymaps.h"
#include "ui/qemu-pixman.h"
#include "ui/console.h"
#include "sysemu/sysemu.h"
#include "ui/input.h"
#include "qapi/error.h"
#include "qemu/main-loop.h"

/*
 * must be last so we get the linux input layer
 * KEY_* defines, not the ncurses ones.
 */
#include <linux/input.h>

/* -------------------------------------------------------------------- */

/* file handles */
static int                        tty = -1, fb = -1, mice = -1;

/* saved state, for restore on exit */
static int                        orig_vtno;
static int                        kd_omode;
static struct vt_mode             vt_omode;
static struct fb_var_screeninfo   fb_ovar;

/* framebuffer */
static struct fb_fix_screeninfo   fb_fix;
static struct fb_var_screeninfo   fb_var;
static uint8_t                   *fb_mem;
static int                        fb_mem_offset;

/* linux console */
static int                        vtno;
static struct vt_mode             vt_mode;
static struct termios             tty_attributes;
static unsigned long              tty_mode;
static unsigned int               tty_flags;
static bool                       tty_mediumraw;
static bool                       key_down[KEY_CNT];

/* console switching */
#define SIG_ACQ      (SIGRTMIN+6)
#define SIG_REL      (SIGRTMIN+7)
#define FB_ACTIVE    0
#define FB_REL_REQ   1
#define FB_INACTIVE  2
#define FB_ACQ_REQ   3
static int fb_switch_state;

/* qemu windup */
static DisplayChangeListener      *dcl;
static int                        resize_screen;
static int                        redraw_screen;
static int                        cx, cy, cw, ch;
static Notifier                   exit_notifier;
static DisplaySurface             *surface;
static pixman_image_t             *sref, *swork;
static pixman_image_t             *framebuffer;
static pixman_transform_t         transform;
static pixman_region16_t          dirty;
static double                     scale;

static QEMUCursor                 *ptr_cursor;
static pixman_image_t             *ptr_image;
static int                        ptr_refresh;
static int                        px, py, pw, ph;
static int                        mx, my, mon;

/* options */
static int                        use_scale;
static pixman_filter_t            pfilter = PIXMAN_FILTER_GOOD;

/* fwd decls */
static int fbdev_activate_vt(int tty, int vtno, bool wait);

/* -------------------------------------------------------------------- */
/* pixman helpers                                                       */

static pixman_image_t *pixman_from_framebuffer(void)
{
    pixman_format_code_t format;
    pixman_image_t *image;
    int type;

    type = qemu_pixman_get_type(fb_var.red.offset,
                                fb_var.green.offset,
                                fb_var.blue.offset);
    format = PIXMAN_FORMAT(fb_var.bits_per_pixel, type,
                           fb_var.transp.length,
                           fb_var.red.length,
                           fb_var.green.length,
                           fb_var.blue.length);
    image = pixman_image_create_bits(format, fb_var.xres, fb_var.yres,
                                     (void *)fb_mem, fb_fix.line_length);
    return image;
}

static pixman_image_t *pixman_image_clone(pixman_image_t *i)
{
    return pixman_image_create_bits(pixman_image_get_format(i),
                                    pixman_image_get_width(i),
                                    pixman_image_get_height(i),
                                    pixman_image_get_data(i),
                                    pixman_image_get_stride(i));
}

/* -------------------------------------------------------------------- */
/* mouse                                                                */

static void read_mouse(void *opaque)
{
    char buf[3];
    int rc, x, y, b;

    rc = read(mice, buf, sizeof(buf));
    if (rc != sizeof(buf)) {
        return;
    }

    if (fb_switch_state != FB_ACTIVE) {
        return;
    }

    x = buf[1];
    y = -buf[2];
    b = buf[0];

    static uint32_t bmap[INPUT_BUTTON__MAX] = {
        [INPUT_BUTTON_LEFT]        = 0x01,
        [INPUT_BUTTON_MIDDLE]      = 0x04,
        [INPUT_BUTTON_RIGHT]       = 0x02,
        [INPUT_BUTTON_WHEEL_UP]    = 0x10,
        [INPUT_BUTTON_WHEEL_DOWN]  = 0x20,
    };
    static uint32_t prev_b;

    if (prev_b != b) {
        qemu_input_update_buttons(dcl->con, bmap, prev_b, b);
        prev_b = b;
    }

    if (qemu_input_is_absolute()) {
        static int ax, ay;
        ax += x; ay += y;
        if (ax < 0) {
            ax = 0;
        }
        if (ay < 0) {
            ay = 0;
        }
        if (ax >= cw*scale) {
            ax = cw*scale-1;
        }
        if (ay >= ch*scale) {
            ay = ch*scale-1;
        }
        qemu_input_queue_abs(dcl->con, INPUT_AXIS_X, ax, 0, cw*scale);
        qemu_input_queue_abs(dcl->con, INPUT_AXIS_Y, ay, 0, ch*scale);
    } else {
        qemu_input_queue_rel(dcl->con, INPUT_AXIS_X, x);
        qemu_input_queue_rel(dcl->con, INPUT_AXIS_Y, y);
    }
    qemu_input_event_sync();
}

static int init_mouse(void)
{
    mice = open("/dev/input/mice", O_RDONLY);
    if (mice == -1) {
        return -1;
    }
    qemu_set_fd_handler(mice, read_mouse, NULL, NULL);
    return 0;
}

static void uninit_mouse(void)
{
    if (mice == -1) {
        return;
    }
    qemu_set_fd_handler(mice, NULL, NULL, NULL);
    close(mice);
    mice = -1;
}

/* -------------------------------------------------------------------- */
/* keyboard                                                             */

static const char *keynames[] = {
#include "linux-keynames.h"
};

static const int scancode_map[KEY_CNT] = {
    [KEY_ESC]           = 0x01,
    [KEY_1]             = 0x02,
    [KEY_2]             = 0x03,
    [KEY_3]             = 0x04,
    [KEY_4]             = 0x05,
    [KEY_5]             = 0x06,
    [KEY_6]             = 0x07,
    [KEY_7]             = 0x08,
    [KEY_8]             = 0x09,
    [KEY_9]             = 0x0a,
    [KEY_0]             = 0x0b,
    [KEY_MINUS]         = 0x0c,
    [KEY_EQUAL]         = 0x0d,
    [KEY_BACKSPACE]     = 0x0e,

    [KEY_TAB]           = 0x0f,
    [KEY_Q]             = 0x10,
    [KEY_W]             = 0x11,
    [KEY_E]             = 0x12,
    [KEY_R]             = 0x13,
    [KEY_T]             = 0x14,
    [KEY_Y]             = 0x15,
    [KEY_U]             = 0x16,
    [KEY_I]             = 0x17,
    [KEY_O]             = 0x18,
    [KEY_P]             = 0x19,
    [KEY_LEFTBRACE]     = 0x1a,
    [KEY_RIGHTBRACE]    = 0x1b,
    [KEY_ENTER]         = 0x1c,

    [KEY_A]             = 0x1e,
    [KEY_S]             = 0x1f,
    [KEY_D]             = 0x20,
    [KEY_F]             = 0x21,
    [KEY_G]             = 0x22,
    [KEY_H]             = 0x23,
    [KEY_J]             = 0x24,
    [KEY_K]             = 0x25,
    [KEY_L]             = 0x26,
    [KEY_SEMICOLON]     = 0x27,
    [KEY_APOSTROPHE]    = 0x28,
    [KEY_GRAVE]         = 0x29,
    [KEY_LEFTSHIFT]     = 0x2a,
    [KEY_BACKSLASH]     = 0x2b,

    [KEY_Z]             = 0x2c,
    [KEY_X]             = 0x2d,
    [KEY_C]             = 0x2e,
    [KEY_V]             = 0x2f,
    [KEY_B]             = 0x30,
    [KEY_N]             = 0x31,
    [KEY_M]             = 0x32,
    [KEY_COMMA]         = 0x33,
    [KEY_DOT]           = 0x34,
    [KEY_SLASH]         = 0x35,
    [KEY_RIGHTSHIFT]    = 0x36,
    [KEY_SPACE]         = 0x39,

    [KEY_F1]            = 0x3b,
    [KEY_F2]            = 0x3c,
    [KEY_F3]            = 0x3d,
    [KEY_F4]            = 0x3e,
    [KEY_F5]            = 0x3f,
    [KEY_F6]            = 0x40,
    [KEY_F7]            = 0x41,
    [KEY_F8]            = 0x42,
    [KEY_F9]            = 0x43,
    [KEY_F10]           = 0x44,
    [KEY_F11]           = 0x57,
    [KEY_F12]           = 0x58,

    [KEY_SYSRQ]         = 0xb7,
    [KEY_SCROLLLOCK]    = 0x46,
#if 0
    [KEY_PAUSE]         = FIXME,
#endif
    [KEY_CAPSLOCK]      = 0x3a,
    [KEY_102ND]         = 0x56,

    [KEY_LEFTCTRL]      = 0x1d,
    [KEY_LEFTMETA]      = 0xdb,
    [KEY_LEFTALT]       = 0x38,
    [KEY_RIGHTALT]      = 0xb8,
    [KEY_RIGHTMETA]     = 0xdc,
    [KEY_RIGHTCTRL]     = 0x9d,
    [KEY_COMPOSE]       = 0xdd,

    [KEY_INSERT]        = 0xd2,
    [KEY_DELETE]        = 0xd3,
    [KEY_HOME]          = 0xc7,
    [KEY_END]           = 0xcf,
    [KEY_PAGEUP]        = 0xc9,
    [KEY_PAGEDOWN]      = 0xd1,

    [KEY_UP]            = 0xc8,
    [KEY_LEFT]          = 0xcb,
    [KEY_RIGHT]         = 0xcd,
    [KEY_DOWN]          = 0xd0,

    [KEY_NUMLOCK]       = 0x45,
    [KEY_KPSLASH]       = 0xb5,
    [KEY_KPASTERISK]    = 0x37,
    [KEY_KP7]           = 0x47,
    [KEY_KP8]           = 0x48,
    [KEY_KP9]           = 0x49,
    [KEY_KPMINUS]       = 0x4a,
    [KEY_KP4]           = 0x4b,
    [KEY_KP5]           = 0x4c,
    [KEY_KP6]           = 0x4d,
    [KEY_KPPLUS]        = 0x4e,
    [KEY_KP1]           = 0x4f,
    [KEY_KP2]           = 0x50,
    [KEY_KP3]           = 0x51,
    [KEY_KP0]           = 0x52,
    [KEY_KPDOT]         = 0x53,
    [KEY_KPENTER]       = 0x9c,
};

static const struct keysym_map {
    int  normal, shifted;
} keysym_map_en_us[KEY_CNT] = {
    [KEY_A] = { .normal = 'a', .shifted = 'A' },
    [KEY_B] = { .normal = 'b', .shifted = 'B' },
    [KEY_C] = { .normal = 'c', .shifted = 'C' },
    [KEY_D] = { .normal = 'd', .shifted = 'D' },
    [KEY_E] = { .normal = 'e', .shifted = 'E' },
    [KEY_F] = { .normal = 'f', .shifted = 'F' },
    [KEY_G] = { .normal = 'g', .shifted = 'G' },
    [KEY_H] = { .normal = 'h', .shifted = 'H' },
    [KEY_I] = { .normal = 'i', .shifted = 'I' },
    [KEY_J] = { .normal = 'j', .shifted = 'J' },
    [KEY_K] = { .normal = 'k', .shifted = 'K' },
    [KEY_L] = { .normal = 'l', .shifted = 'L' },
    [KEY_M] = { .normal = 'm', .shifted = 'M' },
    [KEY_N] = { .normal = 'n', .shifted = 'N' },
    [KEY_O] = { .normal = 'o', .shifted = 'O' },
    [KEY_P] = { .normal = 'p', .shifted = 'P' },
    [KEY_Q] = { .normal = 'q', .shifted = 'Q' },
    [KEY_R] = { .normal = 'r', .shifted = 'R' },
    [KEY_S] = { .normal = 's', .shifted = 'S' },
    [KEY_T] = { .normal = 't', .shifted = 'T' },
    [KEY_U] = { .normal = 'u', .shifted = 'U' },
    [KEY_V] = { .normal = 'v', .shifted = 'V' },
    [KEY_W] = { .normal = 'w', .shifted = 'W' },
    [KEY_X] = { .normal = 'x', .shifted = 'X' },
    [KEY_Y] = { .normal = 'y', .shifted = 'Y' },
    [KEY_Z] = { .normal = 'z', .shifted = 'Z' },

    [KEY_1] = { .normal = '1', .shifted = '!' },
    [KEY_2] = { .normal = '2', .shifted = '@' },
    [KEY_3] = { .normal = '3', .shifted = '#' },
    [KEY_4] = { .normal = '4', .shifted = '$' },
    [KEY_5] = { .normal = '5', .shifted = '%' },
    [KEY_6] = { .normal = '6', .shifted = '^' },
    [KEY_7] = { .normal = '7', .shifted = '&' },
    [KEY_8] = { .normal = '8', .shifted = '*' },
    [KEY_9] = { .normal = '9', .shifted = '(' },
    [KEY_0] = { .normal = '0', .shifted = ')' },

    [KEY_MINUS]       = { .normal = '-',  .shifted = '_'  },
    [KEY_EQUAL]       = { .normal = '=',  .shifted = '+'  },
    [KEY_TAB]         = { .normal = '\t'  },
    [KEY_LEFTBRACE]   = { .normal = '[',  .shifted = '{'  },
    [KEY_RIGHTBRACE]  = { .normal = ']',  .shifted = '}'  },
    [KEY_ENTER]       = { .normal = '\n', },
    [KEY_SEMICOLON]   = { .normal = ';',  .shifted = ':'  },
    [KEY_APOSTROPHE]  = { .normal = '"',  .shifted = '\'' },
    [KEY_BACKSLASH]   = { .normal = '\\', .shifted = '|'  },
    [KEY_COMMA]       = { .normal = ',',  .shifted = '<'  },
    [KEY_DOT]         = { .normal = '.',  .shifted = '>'  },
    [KEY_SLASH]       = { .normal = '/',  .shifted = '?'  },
    [KEY_SPACE]       = { .normal = ' '   },

    [KEY_BACKSPACE]   = { .normal = QEMU_KEY_BACKSPACE  },
    [KEY_UP]          = { .normal = QEMU_KEY_UP         },
    [KEY_DOWN]        = { .normal = QEMU_KEY_DOWN       },
    [KEY_LEFT]        = { .normal = QEMU_KEY_LEFT       },
    [KEY_RIGHT]       = { .normal = QEMU_KEY_RIGHT      },
};

static void start_mediumraw(int tty)
{
    struct termios tattr;

    if (tty_mediumraw) {
        return;
    }
    //trace_fbdev_kbd_raw(1);

    /* save state */
    tcgetattr(tty, &tty_attributes);
    ioctl(tty, KDGKBMODE, &tty_mode);
    tty_flags = fcntl(tty, F_GETFL, NULL);

    /* setup */
    tattr = tty_attributes;
    tattr.c_cflag &= ~(IXON|IXOFF);
    tattr.c_lflag &= ~(ICANON|ECHO|ISIG);
    tattr.c_iflag = 0;
    tattr.c_cc[VMIN] = 1;
    tattr.c_cc[VTIME] = 0;
    tcsetattr(tty, TCSAFLUSH, &tattr);
    ioctl(tty, KDSKBMODE, K_MEDIUMRAW);
    fcntl(tty, F_SETFL, tty_flags | O_NONBLOCK);

    tty_mediumraw = true;
}

static void stop_mediumraw(int tty)
{
    if (!tty_mediumraw) {
        return;
    }
    //trace_fbdev_kbd_raw(0);

    /* restore state */
    tcsetattr(tty, TCSANOW, &tty_attributes);
    ioctl(tty, KDSKBMODE, tty_mode);
    fcntl(tty, F_SETFL, tty_flags);

    tty_mediumraw = false;
}

static void send_scancode(int keycode, int up)
{
    int scancode = scancode_map[keycode];

    if (!scancode) {
        fprintf(stderr, "%s: unmapped key: 0x%x %s\n",
                __func__, keycode, keynames[keycode]);
        return;
    }
    if (scancode & SCANCODE_GREY) {
        qemu_input_event_send_key_number(NULL, SCANCODE_EMUL0, true);
    }
    if (up) {
        qemu_input_event_send_key_number(NULL, scancode, false);
    } else {
        qemu_input_event_send_key_number(NULL, scancode, true);
    }

}

static void send_keysym(int keycode, int shift)
{
    const struct keysym_map *keysym_map = keysym_map_en_us;
    int keysym;

    if (shift && keysym_map[keycode].shifted) {
        keysym = keysym_map[keycode].shifted;
    } else if (keysym_map[keycode].normal) {
        keysym = keysym_map[keycode].normal;
    } else {
        fprintf(stderr, "%s: unmapped key: 0x%x %s\n",
                __func__, keycode, keynames[keycode]);
        return;
    }
    kbd_put_keysym(keysym);
}

static void reset_keys(void)
{
    int keycode;

    for (keycode = 0; keycode < KEY_MAX; keycode++) {
        if (key_down[keycode]) {
            if (qemu_console_is_graphic(NULL)) {
                send_scancode(keycode, 1);
            }
            key_down[keycode] = false;
        }
    }
}

static void read_mediumraw(void *opaque)
{
    uint8_t buf[32];
    int i, rc, up, keycode;
    bool ctrl, alt, shift;

    rc = read(tty, buf, sizeof(buf));
    switch (rc) {
    case -1:
        perror("read tty");
        goto err;
    case 0:
        fprintf(stderr, "%s: eof\n", __func__);
        goto err;
    default:
        for (i = 0; i < rc; i++) {
            up      = buf[i] & 0x80;
            keycode = buf[i] & 0x7f;
            if (keycode == 0) {
                keycode  = (buf[i+1] & 0x7f) << 7;
                keycode |= buf[i+2] & 0x7f;
                i += 2;
            }
            if (keycode > KEY_MAX) {
                continue;
            }

            if (up) {
                if (!key_down[keycode]) {
                    continue;
                }
                key_down[keycode] = false;
            } else {
                key_down[keycode] = true;
            }

            //trace_fbdev_kbd_event(keycode, keynames[keycode], !up);

            alt   = key_down[KEY_LEFTALT]   || key_down[KEY_RIGHTALT];
            ctrl  = key_down[KEY_LEFTCTRL]  || key_down[KEY_RIGHTCTRL];
            shift = key_down[KEY_LEFTSHIFT] || key_down[KEY_RIGHTSHIFT];

            if (ctrl && alt && !up) {
                if (keycode == KEY_ESC) {
                    fprintf(stderr, "=== fbdev emergency escape "
                            "(ctrl-alt-esc) ===\n");
                    exit(1);
                }
                if (keycode == KEY_S) {
                    use_scale = !use_scale;
                    resize_screen++;
                    redraw_screen++;
                    continue;
                }
                if (keycode >= KEY_F1 && keycode <= KEY_F10) {
                    fbdev_activate_vt(tty, keycode+1-KEY_F1, false);
                    key_down[keycode] = false;
                    continue;
                }
                if (keycode >= KEY_1 && keycode <= KEY_9) {
                    console_select(keycode-KEY_1);
                    reset_keys();
                    continue;
                }
            }

            if (qemu_console_is_graphic(NULL)) {
                send_scancode(keycode, up);
            } else if (!up) {
                send_keysym(keycode, shift);
            }
        }
    }
    return;

err:
    exit(1);
}

/* -------------------------------------------------------------------- */

static void fbdev_cls(void)
{
    memset(fb_mem + fb_mem_offset, 0, fb_fix.line_length * fb_var.yres);
}

static int fbdev_activate_vt(int tty, int vtno, bool wait)
{
    //trace_fbdev_vt_activate(vtno, wait);

    if (ioctl(tty, VT_ACTIVATE, vtno) < 0) {
        perror("ioctl VT_ACTIVATE");
        return -1;
    }

    if (wait) {
        if (ioctl(tty, VT_WAITACTIVE, vtno) < 0) {
            perror("ioctl VT_WAITACTIVE");
            return -1;
        }
        //trace_fbdev_vt_activated();
    }

    return 0;
}

static void fbdev_cleanup(void)
{
    //trace_fbdev_cleanup();

    /* release pixman stuff */
    pixman_region_fini(&dirty);
    if (framebuffer) {
        pixman_image_unref(framebuffer);
        framebuffer = NULL;
    }
    if (sref) {
        pixman_image_unref(sref);
        sref = NULL;
    }
    if (swork) {
        pixman_image_unref(swork);
        swork = NULL;
    }

    /* restore console */
    if (fb_mem != NULL) {
        munmap(fb_mem, fb_fix.smem_len+fb_mem_offset);
        fb_mem = NULL;
    }
    if (fb != -1) {
        if (ioctl(fb, FBIOPUT_VSCREENINFO, &fb_ovar) < 0) {
            perror("ioctl FBIOPUT_VSCREENINFO");
        }
        close(fb);
        fb = -1;
    }

    if (tty != -1) {
        stop_mediumraw(tty);
        if (ioctl(tty, KDSETMODE, kd_omode) < 0) {
            perror("ioctl KDSETMODE");
        }
        if (ioctl(tty, VT_SETMODE, &vt_omode) < 0) {
            perror("ioctl VT_SETMODE");
        }
        if (orig_vtno) {
            fbdev_activate_vt(tty, orig_vtno, true);
        }
        qemu_set_fd_handler(tty, NULL, NULL, NULL);
        close(tty);
        tty = -1;
    }
}

static int fbdev_init(const char *device, Error **err)
{
    struct vt_stat vts;
    unsigned long page_mask;
    char ttyname[32];

    /* open framebuffer */
    if (device == NULL) {
        device = getenv("FRAMEBUFFER");
    }
    if (device == NULL) {
        device = "/dev/fb0";
    }
    fb = open(device, O_RDWR);
    if (fb == -1) {
        //error_setg(err, "open %s: %s\n", device, strerror(errno));
        return -1;
    }

    /* open virtual console */
    tty = 0;
    if (ioctl(tty, VT_GETSTATE, &vts) < 0) {
        fprintf(stderr, "Not started from virtual terminal, "
                "trying to open one.\n");

        snprintf(ttyname, sizeof(ttyname), "/dev/tty0");
        tty = open(ttyname, O_RDWR);
        if (tty == -1) {
            //error_setg(err, "open %s: %s\n", ttyname, strerror(errno));
            goto err_early;
        }
        if (ioctl(tty, VT_OPENQRY, &vtno) < 0) {
            //error_setg(err, "ioctl VT_OPENQRY: %s\n", strerror(errno));
            goto err_early;
        }
        if (ioctl(tty, VT_GETSTATE, &vts) < 0) {
            //error_setg(err, "ioctl VT_GETSTATE: %s\n", strerror(errno));
            goto err_early;
        }
        close(tty);

        snprintf(ttyname, sizeof(ttyname), "/dev/tty%d", vtno);
        tty = open(ttyname, O_RDWR);
        if (tty == -1) {
            //error_setg(err, "open %s: %s\n", ttyname, strerror(errno));
            goto err_early;
        }
        orig_vtno = vts.v_active;
        fprintf(stderr, "Switching to vt %d (current %d).\n", vtno, orig_vtno);
    } else {
        orig_vtno = 0;
        vtno = vts.v_active;
        fprintf(stderr, "Started at vt %d, using it.\n", vtno);
    }
    fbdev_activate_vt(tty, vtno, true);

    /* get current settings (which we have to restore) */
    if (ioctl(fb, FBIOGET_VSCREENINFO, &fb_ovar) < 0) {
        //error_setg(err, "ioctl FBIOGET_VSCREENINFO: %s\n", strerror(errno));
        goto err_early;
    }
    if (ioctl(tty, KDGETMODE, &kd_omode) < 0) {
        //error_setg(err, "ioctl KDGETMODE: %s\n", strerror(errno));
        goto err_early;
    }
    if (ioctl(tty, VT_GETMODE, &vt_omode) < 0) {
        //error_setg(err, "ioctl VT_GETMODE: %s\n", strerror(errno));
        goto err_early;
    }

    /* checks & initialisation */
    if (ioctl(fb, FBIOGET_FSCREENINFO, &fb_fix) < 0) {
        //error_setg(err, "ioctl : %s\n", strerror(errno));
        perror("ioctl FBIOGET_FSCREENINFO");
        goto err;
    }
    if (ioctl(fb, FBIOGET_VSCREENINFO, &fb_var) < 0) {
        //error_setg(err, "ioctl FBIOGET_VSCREENINFO: %s\n", strerror(errno));
        goto err;
    }
    if (fb_fix.type != FB_TYPE_PACKED_PIXELS) {
        //error_setg(err, "can handle only packed pixel frame buffers\n");
        goto err;
    }
    switch (fb_var.bits_per_pixel) {
    case 32:
        break;
    default:
        //error_setg(err, "can't handle %d bpp frame buffers\n",
                //fb_var.bits_per_pixel);
        goto err;
    }

    page_mask = getpagesize()-1;
    fb_switch_state = FB_ACTIVE;
    fb_mem_offset = (unsigned long)(fb_fix.smem_start) & page_mask;
    fb_mem = mmap(NULL, fb_fix.smem_len+fb_mem_offset,
                  PROT_READ|PROT_WRITE, MAP_SHARED, fb, 0);
    if (fb_mem == MAP_FAILED) {
        //error_setg(err, "mmap: %s\n", strerror(errno));
        goto err;
    }
    /* move viewport to upper left corner */
    if (fb_var.xoffset != 0 || fb_var.yoffset != 0) {
        fb_var.xoffset = 0;
        fb_var.yoffset = 0;
        if (ioctl(fb, FBIOPAN_DISPLAY, &fb_var) < 0) {
            //error_setg(err, "ioctl FBIOPAN_DISPLAY: %s\n", strerror(errno));
            goto err;
        }
    }
    if (ioctl(tty, KDSETMODE, KD_GRAPHICS) < 0) {
        //error_setg(err, "ioctl KDSETMODE: %s\n", strerror(errno));
        goto err;
    }
    /* some fb drivers need this again after switching to graphics ... */
    fbdev_activate_vt(tty, vtno, true);

    fbdev_cls();

    start_mediumraw(tty);
    qemu_set_fd_handler(tty, read_mediumraw, NULL, NULL);

    framebuffer = pixman_from_framebuffer();
    pixman_region_init(&dirty);
    return 0;

err_early:
    if (tty > 0) {
        close(tty);
    }
    close(fb);
    return -1;

err:
    fbdev_cleanup();
    return -1;
}

static void
fbdev_catch_fatal_signal(int signr)
{
    fprintf(stderr, "%s: %s, restoring linux console state ...\n",
            __func__, strsignal(signr));
    fbdev_cleanup();
    signal(SIGABRT, SIG_DFL);
    fprintf(stderr, "%s: ... done, going abort() now.\n", __func__);
    abort();
}

static void fbdev_catch_exit_signals(void)
{
    static const int signals[] = {
        SIGQUIT, SIGILL, SIGABRT, SIGFPE, SIGSEGV, SIGBUS
    };
    struct sigaction act, old;
    int i;

    memset(&act, 0, sizeof(act));
    act.sa_handler = fbdev_catch_fatal_signal;
    act.sa_flags = SA_RESETHAND;
    sigemptyset(&act.sa_mask);
    for (i = 0; i < ARRAY_SIZE(signals); i++) {
        sigaction(signals[i], &act, &old);
    }
}

/* -------------------------------------------------------------------- */
/* console switching                                                    */

static void fbdev_switch_signal(int signal)
{
    if (signal == SIG_REL) {
        /* release */
        //trace_fbdev_vt_release_request();
        fb_switch_state = FB_REL_REQ;
    }
    if (signal == SIG_ACQ) {
        /* acquisition */
        //trace_fbdev_vt_aquire_request();
        fb_switch_state = FB_ACQ_REQ;
    }
}

static void fbdev_switch_release(void)
{
    stop_mediumraw(tty);
    ioctl(tty, KDSETMODE, kd_omode);
    ioctl(tty, VT_RELDISP, 1);
    fb_switch_state = FB_INACTIVE;
    //trace_fbdev_vt_released();
}

static void fbdev_switch_acquire(void)
{
    ioctl(tty, VT_RELDISP, VT_ACKACQ);
    start_mediumraw(tty);
    reset_keys();
    ioctl(tty, KDSETMODE, KD_GRAPHICS);
    fb_switch_state = FB_ACTIVE;
    //trace_fbdev_vt_aquired();
}

static int fbdev_switch_init(void)
{
    struct sigaction act, old;

    memset(&act, 0, sizeof(act));
    act.sa_handler  = fbdev_switch_signal;
    sigemptyset(&act.sa_mask);
    sigaction(SIG_REL, &act, &old);
    sigaction(SIG_ACQ, &act, &old);

    if (ioctl(tty, VT_GETMODE, &vt_mode) < 0) {
        perror("ioctl VT_GETMODE");
        exit(1);
    }
    vt_mode.mode   = VT_PROCESS;
    vt_mode.waitv  = 0;
    vt_mode.relsig = SIG_REL;
    vt_mode.acqsig = SIG_ACQ;

    if (ioctl(tty, VT_SETMODE, &vt_mode) < 0) {
        perror("ioctl VT_SETMODE");
        exit(1);
    }
    return 0;
}

/* -------------------------------------------------------------------- */
/* rendering                                                            */

static void fbdev_render(void)
{
    assert(surface);

    pixman_image_set_clip_region(swork, &dirty);
    pixman_image_composite(PIXMAN_OP_SRC, swork, NULL, framebuffer,
                           0, 0, 0, 0, 0, 0, fb_var.xres, fb_var.yres);
    pixman_region_fini(&dirty);
    pixman_region_init(&dirty);
}

static void fbdev_unrender_ptr(void)
{
    if (!pw && !ph) {
        return;
    }
    pixman_region_union_rect(&dirty, &dirty, px, py, pw, ph);
    ph = pw = 0;
}

static void fbdev_render_ptr(void)
{
    pixman_region16_t region;
    pixman_transform_t transform;

    if (!mon || !ptr_image) {
        return;
    }
    if (mx < 0 || mx >= cw || my < 0 || my >= ch) {
        return;
    }

    px = mx - ptr_cursor->hot_x;
    py = my - ptr_cursor->hot_y;
    pw = ptr_cursor->width;
    ph = ptr_cursor->height;

    pixman_transform_init_identity(&transform);
    pixman_transform_translate(&transform, NULL,
                               pixman_int_to_fixed(-cx),
                               pixman_int_to_fixed(-cy));
    if (use_scale) {
        pixman_transform_scale(&transform, NULL,
                               pixman_double_to_fixed(1/scale),
                               pixman_double_to_fixed(1/scale));
    }
    pixman_transform_translate(&transform, NULL,
                               pixman_int_to_fixed(-px),
                               pixman_int_to_fixed(-py));
    pixman_image_set_transform(ptr_image, &transform);

    pixman_region_init_rect(&region, 0, 0, pw, ph);
    pixman_image_set_clip_region(ptr_image, &region);

    pixman_image_composite(PIXMAN_OP_OVER, ptr_image, NULL, framebuffer,
                           0, 0, 0, 0, 0, 0, fb_var.xres, fb_var.yres);

    pixman_region_fini(&region);
    ptr_refresh = 0;
}

/* -------------------------------------------------------------------- */
/* qemu interfaces                                                      */

static void fbdev_update(DisplayChangeListener *dcl,
                         int x, int y, int w, int h)
{
    if (fb_switch_state != FB_ACTIVE) {
        return;
    }

    if (resize_screen) {
        double xs, ys;

        //trace_fbdev_dpy_resize(surface_width(surface), surface_height(surface));
        resize_screen = 0;
        cx = 0; cy = 0;
        cw = surface_width(surface);
        ch = surface_height(surface);

        if (use_scale) {
            xs = (double)fb_var.xres / cw;
            ys = (double)fb_var.yres / ch;
            if (xs > ys) {
                scale = ys;
                cx = (fb_var.xres - surface_width(surface)*scale) / 2;
            } else {
                scale = xs;
                cy = (fb_var.yres - surface_height(surface)*scale) / 2;
            }
        } else {
            scale = 1;
            if (surface_width(surface) < fb_var.xres) {
                cx = (fb_var.xres - surface_width(surface)) / 2;
            }
            if (surface_height(surface) < fb_var.yres) {
                cy = (fb_var.yres - surface_height(surface)) / 2;
            }
        }
        if (sref) {
            pixman_image_unref(sref);
        }
        sref = pixman_image_ref(surface->image);

        if (swork) {
            pixman_image_unref(swork);
        }
        swork = pixman_image_clone(sref);

        pixman_transform_init_identity(&transform);
        pixman_transform_translate(&transform, NULL,
                                   pixman_int_to_fixed(-cx),
                                   pixman_int_to_fixed(-cy));
        if (use_scale) {
            pixman_transform_scale(&transform, NULL,
                                   pixman_double_to_fixed(1/scale),
                                   pixman_double_to_fixed(1/scale));
        }
        pixman_image_set_transform(swork, &transform);

        pixman_image_set_filter(swork, pfilter, NULL, 0);
    }

    if (redraw_screen) {
        //trace_fbdev_dpy_redraw();
        redraw_screen = 0;
        fbdev_cls();
        x = 0; y = 0; w = surface_width(surface); h = surface_height(surface);
    }

    pixman_region_union_rect(&dirty, &dirty, x, y, w, h);
    if (ptr_image && mon && pw && ph) {
        ptr_refresh++;
    }
}

static void fbdev_switch(DisplayChangeListener *dcl,
                         DisplaySurface *new_surface)
{
    surface = new_surface,
    resize_screen++;
    redraw_screen++;
}

static void fbdev_refresh(DisplayChangeListener *dcl)
{
    switch (fb_switch_state) {
    case FB_REL_REQ:
        fbdev_switch_release();
        /* fall though */
    case FB_INACTIVE:
        return;
    case FB_ACQ_REQ:
        fbdev_switch_acquire();
        redraw_screen++;
        /* fall though */
    case FB_ACTIVE:
        break;
    }

    graphic_hw_update(NULL);
    if (redraw_screen) {
        fbdev_update(dcl, 0, 0, 0, 0);
    }

    if (ptr_refresh) {
        fbdev_unrender_ptr();
    }
    if (pixman_region_not_empty(&dirty)) {
        fbdev_render();
    }
    if (ptr_refresh) {
        fbdev_render_ptr();
    }
}

static void fbdev_mouse_set(DisplayChangeListener *dcl, int x, int y, int on)
{
    ptr_refresh++;
    mx = x;
    my = y;
    mon = on;
}

static void fbdev_cursor_define(DisplayChangeListener *dcl, QEMUCursor *cursor)
{
    ptr_refresh++;

    if (ptr_cursor) {
        cursor_put(ptr_cursor);
        ptr_cursor = NULL;
    }
    if (ptr_image) {
        pixman_image_unref(ptr_image);
        ptr_image = NULL;
    }

    if (!cursor) {
        return;
    }

    ptr_cursor = cursor;
    cursor_get(ptr_cursor);
    ptr_image = pixman_image_create_bits(PIXMAN_a8r8g8b8,
                                         cursor->width, cursor->height,
                                         cursor->data,
                                         cursor->width * 4);
    pixman_image_set_filter(ptr_image, pfilter, NULL, 0);
}

static const DisplayChangeListenerOps fbdev_ops = {
    .dpy_name          = "fbdev",
    .dpy_gfx_update    = fbdev_update,
    .dpy_gfx_switch    = fbdev_switch,
    .dpy_refresh       = fbdev_refresh,
    .dpy_mouse_set     = fbdev_mouse_set,
    .dpy_cursor_define = fbdev_cursor_define,
};

static void fbdev_exit_notifier(Notifier *notifier, void *data)
{
    fbdev_cleanup();
}

void fbdev_display_init(DisplayState *ds, DisplayOptions *o)
{
    if (dcl != NULL) {
        return;
    }

    if (fbdev_init(NULL, NULL) != 0) {
        exit(-1);
    }
    exit_notifier.notify = fbdev_exit_notifier;
    qemu_add_exit_notifier(&exit_notifier);
    fbdev_switch_init();
    fbdev_catch_exit_signals();
    init_mouse();
    use_scale = false;

    dcl = g_new0(DisplayChangeListener, 1);
    dcl->ops = &fbdev_ops;
    register_displaychangelistener(dcl);

    //trace_fbdev_enabled();
    atexit(fbdev_display_uninit);
}

void fbdev_display_uninit(void)
{
    if (dcl == NULL) {
        return;
    }

    unregister_displaychangelistener(dcl);
    g_free(dcl);
    dcl = NULL;

    fbdev_cleanup();
    qemu_remove_exit_notifier(&exit_notifier);
    uninit_mouse();
}

static QemuDisplay qemu_display_fbdev = {
    .type       = DISPLAY_TYPE_FBDEV,
    .init       = fbdev_display_init,
};

static void register_fbdev(void)
{
    qemu_display_register(&qemu_display_fbdev);
}

type_init(register_fbdev);
