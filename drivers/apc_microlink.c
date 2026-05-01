/*  apc_microlink.c - Driver for APC MicroLink USB HID protocol UPS
 *
 *  Copyright © 2026 r0ps3c <rudolph+gh@faex.net>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 */

#include "main.h"
#include "usb-common.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#if !WITH_LIBUSB_1_0
# error "apc_microlink requires libusb-1.0 (configure with --with-usb)"
#endif

#define DRIVER_NAME	"APC MicroLink USB HID driver"
#define DRIVER_VERSION	"0.02"

#define APC_VENDORID		0x051d
#define APC_PRODUCTID		0x0003

/* PCSS HID report IDs */
#define PCSS_REPORT_OUT		0x90
#define PCSS_REPORT_IN		0x89
#define PCSS_ENDPOINT		1
#define PCSS_IFACE		0
#define PCSS_REPORT_LEN		64
#define PCSS_ROW_LEN		32

/* PCSS stream commands sent to device */
#define PCSS_CMD_RESET		0xf7	/* reset device stream to beginning */
#define PCSS_CMD_START		0xfd	/* start/continue streaming */
#define PCSS_CMD_ACK		0xfe	/* acknowledge a row and request next */

/* Row numbers in the PCSS pre-auth zone */
#define PCSS_ROW_HEADER		0x00	/* device header (auth prerequisite) */
#define PCSS_ROW_SERIAL		0x40	/* serial/model (auth prerequisite) */
#define PCSS_ROW_MASTER_KEY	0x65	/* master handshake key (auth prerequisite) */
/* Row 0x68 appears in both pre-auth (auth trigger) and telemetry zones;
 * distinguished by whether PCSS_ROW_MASTER_KEY was seen in the same call. */
#define PCSS_ROW_AUTH_TRIGGER	0x68

upsdrv_info_t upsdrv_info = {
	DRIVER_NAME,
	DRIVER_VERSION,
	"r0ps3c <rudolph+gh@faex.net>",
	DRV_EXPERIMENTAL,
	{ NULL }
};

/* USB device ID table; parsed by nut-usbinfo.pl for nut-scanner integration */
static usb_device_id_t apc_microlink_usb_device_table[] = {
	{ USB_DEVICE(APC_VENDORID, APC_PRODUCTID), NULL },
	/* Terminating entry */
	{ 0, 0, NULL }
};

typedef enum {
	PCSS_VALUE_U16,
	PCSS_VALUE_U32
} pcss_value_type_t;

typedef struct {
	const char *nutvar;
	uint8_t row;
	uint8_t off;
	pcss_value_type_t type;
	unsigned int binpoint;
	const char *fmt;
} pcss_telemetry_map_t;

typedef struct {
	uint8_t header[8];
	uint8_t serial[16];
	uint8_t master[4];
	int have_header;
	int have_serial;
	int have_master;
	int authenticated;
} pcss_auth_state_t;

typedef struct {
	uint8_t row[256][32];
	uint8_t seen[256];
} pcss_rows_t;

static usb_dev_handle *usb_handle = NULL;
static int opt_bus = -1;
static int opt_dev = -1;
static int opt_reads = 80;
static int opt_min_reads = 8;
static int opt_startup_reads = 240;
static int opt_timeout_ms = 1000;
static int opt_auth_delay_ms = 18;
static int opt_full_poll = 0;
static int opt_raw_rows = 0;
static int opt_reset_on_auth_fail = 0;
static int opt_reset_on_recover = 0;
static int opt_reconnect = 1;
static int startup_use_f7 = 1;
static int have_startup_telemetry = 0;
static pcss_auth_state_t auth_state;
static pcss_rows_t rows;

static const pcss_telemetry_map_t telemetry_map[] = {
	{ "input.voltage",	0x5d, 0x1c, PCSS_VALUE_U16, 6,  "%.1f" },
	{ "input.frequency",	0x5d, 0x1e, PCSS_VALUE_U16, 7,  "%.1f" },
	{ "output.voltage",	0x5e, 0x04, PCSS_VALUE_U16, 6,  "%.2f" },
	{ "output.current",	0x5e, 0x06, PCSS_VALUE_U16, 5,  "%.1f" },
	{ "output.frequency",	0x5e, 0x08, PCSS_VALUE_U16, 7,  "%.1f" },
	{ "ups.load",		0x5d, 0x10, PCSS_VALUE_U16, 8,  "%.1f" },
	{ "battery.voltage",	0x5e, 0x0e, PCSS_VALUE_U16, 5,  "%.1f" },
	{ "battery.temperature",0x5e, 0x10, PCSS_VALUE_U16, 7,  "%.1f" },
	{ "battery.charge",	0x66, 0x04, PCSS_VALUE_U16, 9,  "%.1f" },
	{ "battery.runtime",	0x66, 0x00, PCSS_VALUE_U32, 0,  "%.0f" },
	{ "experimental.apc_microlink.load_power_percent",
				0x5d, 0x0e, PCSS_VALUE_U16, 8,  "%.1f" },
	{ NULL, 0, 0, PCSS_VALUE_U16, 0, NULL }
};

static void fletcher_update(uint8_t *s0, uint8_t *s1, const uint8_t *data, size_t len)
{
	size_t i;
	unsigned int a = *s0;
	unsigned int b = *s1;

	for (i = 0; i < len; i++) {
		a = (a + data[i]) % 255;
		b = (b + a) % 255;
	}

	*s0 = (uint8_t)a;
	*s1 = (uint8_t)b;
}

static void pcss_message_checksum(const uint8_t *data, size_t len, uint8_t out[2])
{
	uint8_t s0 = 0;
	uint8_t s1 = 0;
	unsigned int c0;
	unsigned int c1;

	fletcher_update(&s0, &s1, data, len);
	c0 = (~((s0 + s1) % 255)) & 0xff;
	c1 = (~((c0 + s0) % 255)) & 0xff;
	out[0] = (uint8_t)c0;
	out[1] = (uint8_t)c1;
}

static void fill_auth_random(uint8_t out[2])
{
#ifndef WIN32
	FILE *fp = fopen("/dev/urandom", "rb");

	if (fp) {
		if (fread(out, 1, 2, fp) == 2) {
			fclose(fp);
			return;
		}
		fclose(fp);
	}
#endif
	out[0] = (uint8_t)(rand() & 0xff);
	out[1] = (uint8_t)((rand() >> 8) & 0xff);
}

static uint16_t word_be(const uint8_t *buf, int word)
{
	return ((uint16_t)buf[word * 2] << 8) | buf[word * 2 + 1];
}

static uint16_t u16_be_at(const uint8_t *buf, int off)
{
	return ((uint16_t)buf[off] << 8) | buf[off + 1];
}

static uint32_t u32_be_at(const uint8_t *buf, int off)
{
	return ((uint32_t)buf[off] << 24) |
		((uint32_t)buf[off + 1] << 16) |
		((uint32_t)buf[off + 2] << 8) |
		(uint32_t)buf[off + 3];
}

static double scale_binary_point(uint32_t raw, unsigned int binpoint)
{
	double divisor = 1.0;

	while (binpoint-- > 0) {
		divisor *= 2.0;
	}

	return (double)raw / divisor;
}

static void row_to_hex(uint8_t rownum, char *out, size_t out_len)
{
	size_t i;
	char *p = out;
	size_t left = out_len;

	if (out_len == 0) {
		return;
	}

	for (i = 0; i < sizeof(rows.row[rownum]) && left > 2; i++) {
		int n = snprintf(p, left, "%02x", rows.row[rownum][i]);
		if (n < 0 || (size_t)n >= left) {
			break;
		}
		p += n;
		left -= (size_t)n;
	}
}

static int send_report(const uint8_t *report)
{
	int transferred = 0;
	int rc;

	upsdebug_hex(4, "PCSS OUT", report, PCSS_REPORT_LEN);
	rc = libusb_interrupt_transfer(usb_handle,
		USB_ENDPOINT_OUT | PCSS_ENDPOINT,
		(unsigned char *)report,
		PCSS_REPORT_LEN,
		&transferred,
		opt_timeout_ms);
	if (rc != LIBUSB_SUCCESS) {
		upsdebugx(1, "interrupt OUT failed: %s", nut_usb_strerror(rc));
		return -1;
	}

	return transferred == PCSS_REPORT_LEN ? 0 : -1;
}

static int send_cmd(uint8_t cmd)
{
	uint8_t report[PCSS_REPORT_LEN] = {0};

	report[0] = PCSS_REPORT_OUT;
	report[1] = cmd;
	return send_report(report);
}

static int pcss_send_start_prompt(void)
{
	if (startup_use_f7 && send_cmd(PCSS_CMD_RESET) < 0) {
		return -1;
	}
	if (startup_use_f7) {
		usleep(2000);
	}
	if (send_cmd(PCSS_CMD_START) < 0) {
		return -1;
	}
	return 0;
}

static int pcss_send_poll_prompt(void)
{
	upsdebugx(2, "requesting MicroLink poll stream");
	return send_cmd(PCSS_CMD_START);
}

static int recv_report(uint8_t *report)
{
	int transferred = 0;
	int rc;

	memset(report, 0, PCSS_REPORT_LEN);
	rc = libusb_interrupt_transfer(usb_handle,
		USB_ENDPOINT_IN | PCSS_ENDPOINT,
		report,
		PCSS_REPORT_LEN,
		&transferred,
		opt_timeout_ms);
	if (rc != LIBUSB_SUCCESS) {
		upsdebugx(2, "interrupt IN failed: %s", nut_usb_strerror(rc));
		if (rc == LIBUSB_ERROR_TIMEOUT) {
			return -2;
		}
		return -1;
	}

	upsdebug_hex(5, "PCSS IN", report, (size_t)transferred);
	return transferred;
}

static void track_row(const uint8_t *report, int len)
{
	uint8_t rownum;

	if (len < 36 || report[0] != PCSS_REPORT_IN) {
		return;
	}

	rownum = report[1];
	memcpy(rows.row[rownum], report + 2, 32);
	rows.seen[rownum] = 1;

	if (rownum == PCSS_ROW_HEADER) {
		memcpy(auth_state.header, report + 2, sizeof(auth_state.header));
		auth_state.have_header = 1;
	} else if (rownum == PCSS_ROW_SERIAL) {
		memcpy(auth_state.serial, report + 2, sizeof(auth_state.serial));
		auth_state.have_serial = 1;
	} else if (rownum == PCSS_ROW_MASTER_KEY) {
		/* SMC1000C descriptor: master handshake usage 2:4.8.6 is row 0x65 offset 0x06. */
		memcpy(auth_state.master, report + 2 + 0x06, sizeof(auth_state.master));
		auth_state.have_master = 1;
	}
}

static int pcss_have_core_update(const uint8_t *seen)
{
	return seen[0x5d] && seen[0x5e] && seen[0x66] && seen[PCSS_ROW_AUTH_TRIGGER];
}

static int build_auth_post(uint8_t post[PCSS_REPORT_LEN])
{
	uint8_t s0;
	uint8_t s1;
	uint8_t csum[2];

	if (!auth_state.have_header || !auth_state.have_serial || !auth_state.have_master) {
		upsdebugx(1, "not enough data for auth POST: header=%d serial=%d master=%d",
			auth_state.have_header, auth_state.have_serial, auth_state.have_master);
		return -1;
	}

	memset(post, 0, PCSS_REPORT_LEN);
	post[0] = PCSS_REPORT_OUT;
	post[1] = 0x65;	/* auth POST report sub-command */
	post[2] = 0x0a;
	post[3] = 0x04;
	fill_auth_random(post + 4);

	s0 = auth_state.header[4];
	s1 = auth_state.header[3];
	fletcher_update(&s0, &s1, auth_state.header, sizeof(auth_state.header));
	fletcher_update(&s0, &s1, auth_state.serial, sizeof(auth_state.serial));
	fletcher_update(&s0, &s1, auth_state.master, 2);
	post[6] = s0;
	post[7] = s1;

	pcss_message_checksum(post + 1, 7, csum);
	post[8] = csum[0];
	post[9] = csum[1];

	upsdebug_hex(2, "PCSS auth POST", post, 10);
	return 0;
}

static int pcss_read_rows(int max_reads, int do_auth)
{
	int i;
	int consecutive_timeouts = 0;
	int rows_seen_this_call = 0;
	int startup_prompts = do_auth ? 1 : 0;
	uint8_t seen_this_call[256] = {0};

	for (i = 0; i < max_reads; i++) {
		uint8_t report[PCSS_REPORT_LEN];
		int len = recv_report(report);

		if (len < 0) {
			if (len == -2) {
				if (++consecutive_timeouts >= 3) {
					if ((do_auth && auth_state.authenticated) ||
					    (!do_auth && rows_seen_this_call > 0)) {
						return 0;
					}
					upsdebugx(1, "too many consecutive MicroLink timeouts");
					return -1;
				}
					if (do_auth && rows_seen_this_call == 0 && startup_prompts < 4) {
						if (pcss_send_start_prompt() < 0) {
							return -1;
						}
						startup_prompts++;
					} else if (!do_auth && rows_seen_this_call == 0) {
						/* No rows yet — trigger a new stream from the device. */
						if (pcss_send_poll_prompt() < 0) {
							return -1;
						}
					} else if (send_cmd(PCSS_CMD_ACK) < 0) {
						/* Rows in progress (startup or poll); keep session alive
						 * without restarting the stream. */
						return -1;
					}
					continue;
			}
			return -1;
		}
		consecutive_timeouts = 0;

		if (len < 2 || report[0] != PCSS_REPORT_IN) {
			if (do_auth && rows_seen_this_call == 0 && startup_prompts < 4) {
				if (pcss_send_start_prompt() < 0) {
					return -1;
				}
				startup_prompts++;
			} else if (!do_auth && rows_seen_this_call == 0) {
				if (pcss_send_poll_prompt() < 0) {
					return -1;
				}
			} else if (send_cmd(PCSS_CMD_ACK) < 0) {
				return -1;
			}
			continue;
		}

			track_row(report, len);
			if (len >= 36) {
				if (do_auth && rows_seen_this_call == 0) {
					upsdebugx(1, "PCSS startup stream began at row 0x%02x", report[1]);
				}
				seen_this_call[report[1]] = 1;
				rows_seen_this_call++;
			}

		if (do_auth && !auth_state.authenticated && report[1] == PCSS_ROW_AUTH_TRIGGER) {
			uint8_t post[PCSS_REPORT_LEN];

			/* Row PCSS_ROW_MASTER_KEY always precedes the auth-trigger
			 * PCSS_ROW_AUTH_TRIGGER in the pre-auth zone.  The telemetry
			 * zone also has a PCSS_ROW_AUTH_TRIGGER but it is NOT preceded
			 * by PCSS_ROW_MASTER_KEY in the same read call.  Require
			 * PCSS_ROW_MASTER_KEY seen this call before sending auth POST
			 * so we never POST to the telemetry PCSS_ROW_AUTH_TRIGGER. */
			if (!seen_this_call[PCSS_ROW_MASTER_KEY]) {
				upsdebugx(1, "PCSS skipping 0x68 auth trigger: row 0x65 not seen this call (telemetry 0x68)");
				if (send_cmd(PCSS_CMD_ACK) < 0) {
					return -1;
				}
				continue;
			}

			if (!auth_state.have_header || !auth_state.have_serial || !auth_state.have_master) {
				upsdebugx(1,
					"PCSS auth trigger before prerequisites: header=%d serial=%d master=%d",
					auth_state.have_header, auth_state.have_serial, auth_state.have_master);
				if (send_cmd(PCSS_CMD_ACK) < 0) {
					return -1;
				}
				continue;
			}

			if (opt_auth_delay_ms > 0) {
				usleep((useconds_t)opt_auth_delay_ms * 1000);
			}
			if (build_auth_post(post) < 0 || send_report(post) < 0) {
				return -1;
			}
			upsdebugx(1, "PCSS authentication POST sent");
			auth_state.authenticated = 1;
			/* Keep reading to drain the post-auth stream so the device
			 * reaches a clean end-of-stream state before we return.
			 * The auth POST acts as the ACK for row 0x68; subsequent
			 * rows (including the 0x65 session echo) need normal ACKs,
			 * which the loop provides once we continue. */
			continue;
		}

			if (send_cmd(PCSS_CMD_ACK) < 0) {
				return -1;
			}

			if (!do_auth &&
			    !opt_full_poll &&
			    rows_seen_this_call >= opt_min_reads &&
			    pcss_have_core_update(seen_this_call)) {
				upsdebugx(2, "PCSS update complete after %d rows", rows_seen_this_call);
				return 0;
			}
		}

	/* Loop exhausted max_reads without a complete core update in poll mode. */
	if (!do_auth && !pcss_have_core_update(seen_this_call)) {
		upsdebugx(1, "MicroLink poll: no core update after %d reads (rows seen: %d)",
			max_reads, rows_seen_this_call);
		return -1;
	}
	return 0;
}

static int pcss_send_startup(void)
{
	return pcss_send_start_prompt();
}

static int pcss_authenticate(void)
{
	int attempt;

	for (attempt = 0; attempt < 2; attempt++) {
		memset(&auth_state, 0, sizeof(auth_state));
		startup_use_f7 = attempt == 0;

		if (pcss_send_startup() < 0) {
			return -1;
		}

		if (pcss_read_rows(opt_startup_reads, 1) == 0 && auth_state.authenticated) {
			return 0;
		}
		if (auth_state.authenticated) {
			return 0;
		}

		upsdebugx(1, "PCSS authentication attempt %d (%s startup) failed, retrying",
			attempt + 1, startup_use_f7 ? "f7/fd" : "fd-only");
		send_cmd(PCSS_CMD_RESET);
		usleep(250000);
	}

	return -1;
}

static int open_matching_device(void)
{
	libusb_device **list = NULL;
	ssize_t n;
	ssize_t i;
	int rc;

	rc = libusb_init(NULL);
	if (rc != LIBUSB_SUCCESS) {
		upslogx(LOG_ERR, "libusb_init failed: %s", nut_usb_strerror(rc));
		return -1;
	}

	n = libusb_get_device_list(NULL, &list);
	if (n < 0) {
		upslogx(LOG_ERR, "libusb_get_device_list failed: %s", nut_usb_strerror((int)n));
		return -1;
	}

	for (i = 0; i < n; i++) {
		struct libusb_device_descriptor desc;
		libusb_device *dev = list[i];

		if (libusb_get_device_descriptor(dev, &desc) != LIBUSB_SUCCESS) {
			continue;
		}
		{
			USBDevice_t udev;
			memset(&udev, 0, sizeof(udev));
			udev.VendorID  = desc.idVendor;
			udev.ProductID = desc.idProduct;
			if (!is_usb_device_supported(apc_microlink_usb_device_table, &udev)) {
				continue;
			}
		}
		if (opt_bus >= 0 && libusb_get_bus_number(dev) != opt_bus) {
			continue;
		}
		if (opt_dev >= 0 && libusb_get_device_address(dev) != opt_dev) {
			continue;
		}

		rc = libusb_open(dev, &usb_handle);
		if (rc != LIBUSB_SUCCESS) {
			upsdebugx(1, "libusb_open failed: %s", nut_usb_strerror(rc));
			continue;
		}

		upslogx(LOG_INFO, "matched APC MicroLink USB device bus=%u dev=%u",
			libusb_get_bus_number(dev), libusb_get_device_address(dev));
		break;
	}

	libusb_free_device_list(list, 1);

	if (!usb_handle) {
		upslogx(LOG_ERR, "no matching APC MicroLink USB device found");
		return -1;
	}

	libusb_set_auto_detach_kernel_driver(usb_handle, 1);

	rc = usb_claim_interface(usb_handle, PCSS_IFACE);
	if (rc == LIBUSB_ERROR_BUSY) {
		/* Auto-detach failed (e.g. container without CAP_SYS_ADMIN); try manual detach. */
		if (libusb_detach_kernel_driver(usb_handle, PCSS_IFACE) == LIBUSB_SUCCESS) {
			rc = usb_claim_interface(usb_handle, PCSS_IFACE);
		}
	}
	if (rc != LIBUSB_SUCCESS) {
		upslogx(LOG_ERR, "claim interface %d failed: %s", PCSS_IFACE, nut_usb_strerror(rc));
		return -1;
	}

	return 0;
}

static void close_device(int send_stop)
{
	if (usb_handle) {
		if (send_stop) {
			(void)send_cmd(PCSS_CMD_RESET);
		}
		usb_release_interface(usb_handle, PCSS_IFACE);
		usb_close(usb_handle);
		usb_handle = NULL;
	}
	libusb_exit(NULL);
}

static int reset_and_reopen_device(void)
{
	int rc;

	if (!usb_handle) {
		return open_matching_device();
	}

	upslogx(LOG_WARNING, "resetting APC MicroLink USB device after authentication failure");
	rc = usb_reset(usb_handle);
	if (rc != LIBUSB_SUCCESS) {
		upslogx(LOG_WARNING, "USB reset returned: %s", nut_usb_strerror(rc));
	}

	close_device(0);
	usleep(2000000);
	return open_matching_device();
}

static int recover_device(void)
{
	int rc;

	if (opt_reset_on_recover && usb_handle) {
		upslogx(LOG_WARNING, "resetting APC MicroLink USB device for recovery");
		rc = usb_reset(usb_handle);
		if (rc != LIBUSB_SUCCESS) {
			upslogx(LOG_WARNING, "USB reset returned: %s", nut_usb_strerror(rc));
		}
		usleep(2000000);
	}

	close_device(0);
	if (open_matching_device() < 0) {
		return -1;
	}
	memset(&auth_state, 0, sizeof(auth_state));
	if (pcss_authenticate() < 0) {
		return -1;
	}
	return 0;
}

static void set_text_from_row(uint8_t rownum, const char *var, int off, int len)
{
	char buf[64];
	int i;

	if (!rows.seen[rownum] || len >= (int)sizeof(buf)) {
		return;
	}

	memcpy(buf, rows.row[rownum] + off, (size_t)len);
	buf[len] = '\0';
	for (i = 0; i < len; i++) {
		if ((unsigned char)buf[i] < 0x20 || (unsigned char)buf[i] > 0x7e) {
			buf[i] = ' ';
		}
	}
	for (i = len - 1; i >= 0 && buf[i] == ' '; i--) {
		buf[i] = '\0';
	}
	dstate_setinfo(var, "%s", buf);
}

static void publish_raw_rows(void)
{
	static const uint8_t interesting[] = {
		0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f, 0x60, 0x61,
		0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68
	};
	size_t i;

	for (i = 0; i < sizeof(interesting); i++) {
		uint8_t rownum = interesting[i];
		char var[64];
		char val[80] = {0};

		if (!rows.seen[rownum]) {
			continue;
		}

		snprintf(var, sizeof(var), "experimental.apc_microlink.row.%02x", rownum);
		row_to_hex(rownum, val, sizeof(val));
		dstate_setinfo(var, "%s", val);
	}
}

static void publish_mapped_telemetry(void)
{
	const pcss_telemetry_map_t *entry;

	for (entry = telemetry_map; entry->nutvar != NULL; entry++) {
		uint32_t raw;
		double value;

		if (!rows.seen[entry->row]) {
			continue;
		}
		if ((entry->type == PCSS_VALUE_U16 && entry->off + 2 > PCSS_ROW_LEN) ||
		    (entry->type == PCSS_VALUE_U32 && entry->off + 4 > PCSS_ROW_LEN)) {
			continue;
		}

		raw = (entry->type == PCSS_VALUE_U16) ?
			u16_be_at(rows.row[entry->row], entry->off) :
			u32_be_at(rows.row[entry->row], entry->off);
		value = scale_binary_point(raw, entry->binpoint);

		if (!strcmp(entry->nutvar, "battery.charge") && value > 100.0) {
			value = 100.0;
		}

		dstate_setinfo(entry->nutvar, entry->fmt, value);
	}
}

static void publish_telemetry(void)
{
	status_init();

	publish_mapped_telemetry();

	if (rows.seen[0x5d]) {
		double input_v = scale_binary_point(u16_be_at(rows.row[0x5d], 0x1c), 6);

		status_set(input_v < 10.0 ? "OB" : "OL");
	} else {
		status_set("OL");
	}

	if (rows.seen[PCSS_ROW_AUTH_TRIGGER]) {
		uint16_t state_a = word_be(rows.row[PCSS_ROW_AUTH_TRIGGER], 10);
		uint16_t state_b = word_be(rows.row[PCSS_ROW_AUTH_TRIGGER], 11);

		dstate_setinfo("experimental.apc_microlink.state_a", "0x%04x", state_a);
		dstate_setinfo("experimental.apc_microlink.state_b", "0x%04x", state_b);
	}

	if (opt_raw_rows) {
		publish_raw_rows();
	}
	status_commit();
	dstate_dataok();
}

void upsdrv_initinfo(void)
{
	dstate_setinfo("ups.mfr", "APC");
	dstate_setinfo("device.mfr", "APC");
	set_text_from_row(PCSS_ROW_SERIAL, "ups.serial", 0, 16);
	set_text_from_row(PCSS_ROW_SERIAL, "device.serial", 0, 16);
	set_text_from_row(PCSS_ROW_SERIAL, "ups.model", 16, 16);
	set_text_from_row(PCSS_ROW_SERIAL, "device.model", 16, 16);
	set_text_from_row(0x43, "ups.firmware", 0, 32);
}

void upsdrv_updateinfo(void)
{
	if (have_startup_telemetry) {
		have_startup_telemetry = 0;
		publish_telemetry();
		return;
	}

	/* The device stays in telemetry mode between polls once authenticated.
	 * Send PCSS_CMD_START to restart the stream and read the next batch. */
	if (send_cmd(PCSS_CMD_START) == 0 &&
	    pcss_read_rows(opt_reads, 0) == 0) {
		publish_telemetry();
		return;
	}

	/* Device returned to pre-auth mode (poll interval exceeded its telemetry
	 * window).  Re-authenticate in place without closing/reopening USB.
	 * Pre-seed auth prerequisites from cached rows so authentication works
	 * even when the stream starts mid-cycle (past rows 0x00 and 0x40). */
	memset(&auth_state, 0, sizeof(auth_state));
	if (rows.seen[PCSS_ROW_HEADER]) {
		memcpy(auth_state.header, rows.row[PCSS_ROW_HEADER], sizeof(auth_state.header));
		auth_state.have_header = 1;
	}
	if (rows.seen[PCSS_ROW_SERIAL]) {
		memcpy(auth_state.serial, rows.row[PCSS_ROW_SERIAL], sizeof(auth_state.serial));
		auth_state.have_serial = 1;
	}
	if (rows.seen[PCSS_ROW_MASTER_KEY]) {
		memcpy(auth_state.master, rows.row[PCSS_ROW_MASTER_KEY] + 0x06, sizeof(auth_state.master));
		auth_state.have_master = 1;
	}
	startup_use_f7 = 0;
	if (pcss_send_startup() == 0 &&
	    pcss_read_rows(opt_startup_reads, 1) == 0 &&
	    auth_state.authenticated) {
		publish_telemetry();
		return;
	}

	if (opt_reconnect && recover_device() == 0) {
		publish_telemetry();
		return;
	}
	dstate_datastale();
}

void upsdrv_shutdown(void)
{
	/* Shutdown commands are not yet implemented for this protocol.
	 * See KNOWN ISSUES in the man page. */
	upslogx(LOG_ERR, "shutdown not supported by apc_microlink yet");
	if (handling_upsdrv_shutdown > 0) {
		set_exit_flag(EF_EXIT_FAILURE);
	}
}

void upsdrv_help(void)
{
}

void upsdrv_tweak_prognames(void)
{
}

void upsdrv_makevartable(void)
{
	/* Standard NUT USB options (vendorid, productid, bus, device, serial, …) */
	nut_usb_addvars();

	addvar(VAR_VALUE, "reads", "Number of HID records to read per update");
	addvar(VAR_VALUE, "min_reads", "Minimum HID records to read before fast polling can stop");
	addvar(VAR_VALUE, "startup_reads", "Number of HID records to read while authenticating");
	addvar(VAR_VALUE, "timeout_ms", "USB interrupt timeout in milliseconds");
	addvar(VAR_VALUE, "auth_delay_ms", "Delay before authentication POST in milliseconds");
	addvar(VAR_FLAG, "full_poll", "Read the full configured reads count on every poll");
	addvar(VAR_FLAG, "raw_rows", "Publish raw MicroLink rows as experimental variables");
	addvar(VAR_FLAG, "no_reconnect", "Do not reopen and reauthenticate after poll failures");
	addvar(VAR_FLAG, "reset_on_auth_fail", "Reset and reopen USB device once if authentication fails");
	addvar(VAR_FLAG, "reset_on_recover", "Reset and reopen USB device before poll failure recovery");
}

void upsdrv_initups(void)
{
	const char *val;
	struct timespec ts;

	warn_if_bad_usb_port_filename(device_path);

	val = getval("bus");
	if (val) {
		opt_bus = atoi(val);
	}
	val = getval("device");
	if (val) {
		opt_dev = atoi(val);
	}
	val = getval("reads");
	if (val) {
		opt_reads = atoi(val);
	}
	val = getval("min_reads");
	if (val) {
		opt_min_reads = atoi(val);
	}
	val = getval("startup_reads");
	if (val) {
		opt_startup_reads = atoi(val);
	}
	val = getval("timeout_ms");
	if (val) {
		opt_timeout_ms = atoi(val);
	}
	val = getval("auth_delay_ms");
	if (val) {
		opt_auth_delay_ms = atoi(val);
	}
	if (testvar("reset_on_auth_fail")) {
		opt_reset_on_auth_fail = 1;
	}
	if (testvar("reset_on_recover")) {
		opt_reset_on_recover = 1;
	}
	if (testvar("full_poll")) {
		opt_full_poll = 1;
	}
	if (testvar("raw_rows")) {
		opt_raw_rows = 1;
	}
	if (testvar("no_reconnect")) {
		opt_reconnect = 0;
	}

	if (opt_reads < 1) {
		opt_reads = 1;
	}
	if (opt_min_reads < 1) {
		opt_min_reads = 1;
	}
	if (opt_startup_reads < 1) {
		opt_startup_reads = 1;
	}
	if (opt_timeout_ms < 100) {
		opt_timeout_ms = 100;
	}
	if (opt_auth_delay_ms < 0) {
		opt_auth_delay_ms = 0;
	}

	clock_gettime(CLOCK_MONOTONIC, &ts);
	srand((unsigned int)(ts.tv_nsec ^ ts.tv_sec ^ getpid()));

	if (open_matching_device() < 0) {
		fatalx(EXIT_FAILURE, "failed to open APC MicroLink USB device");
	}

	if (pcss_authenticate() < 0) {
		if (!opt_reset_on_auth_fail ||
		    reset_and_reopen_device() < 0 ||
		    pcss_authenticate() < 0) {
			fatalx(EXIT_FAILURE, "failed to authenticate APC MicroLink session");
		}
	}

	have_startup_telemetry = 1;
	publish_telemetry();
}

void upsdrv_cleanup(void)
{
	close_device(1);
}
