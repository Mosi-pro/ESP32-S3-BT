/*
 * ESP32_S3_Bluetooth_Dongle.ino
 *
 * ESP32-S3 als USB-Bluetooth-HCI-Adapter ("Bluetooth Radio") fuer Windows.
 *
 * Funktionsprinzip (Bluetooth Core Spec Vol 4 Part B, "HCI over USB"):
 *   Windows  <-- USB (Device-Class 0xE0/0x01/0x01) -->  ESP32-S3  <-- VHCI -->  BLE-Controller
 *
 *   - USB-Descriptor: Wireless Controller / RF / Bluetooth Programming Interface.
 *     Windows bindet dafuer den Inbox-Treiber (bthusb.sys, "Generic Bluetooth Adapter").
 *   - HCI-Kommandos kommen per USB-Control-Request (Class, Device), HCI-Events gehen ueber
 *     den Interrupt-IN-Endpoint, ACL-Daten laufen ueber Bulk-OUT/Bulk-IN.
 *   - Die Firmware ist eine reine Bruecke: Windows' Bluetooth-Stack (Host) spricht ueber
 *     VHCI direkt mit dem BLE-Controller des ESP32-S3. Es werden keine HCI-Antworten erfunden.
 *
 * Grenzen des ESP32-S3 (Hardware, nicht aenderbar):
 *   - Nur Bluetooth LE (5.x). KEIN Bluetooth Classic (BR/EDR): kein A2DP/HFP/SPP, keine
 *     Classic-Inquiry, keine Classic-Kopfhoerer/-Tastaturen/-Maeuse/-Controller.
 *   - Kein SCO/eSCO und keine LE-Isochronous-Channels: kein Audio ueber diesen Adapter.
 *   - Die SCO-Alt-Settings im USB-Descriptor sind nur deklariert (Windows erwartet sie bei
 *     Bluetooth-Dongles), die Endpoints werden nie geoeffnet und der Controller meldet kein SCO.
 *
 * Arduino-Einstellungen (siehe Anleitung):
 *   Board: ESP32S3 Dev Module | USB Mode: USB-OTG (TinyUSB) | USB CDC On Boot: Disabled
 *   Serial-Monitor = UART-Buchse des Boards (115200 Baud). Windows-Anschluss = "USB"-Buchse (nativ).
 *
 * Getestet gegen die Quelltexte von Arduino-ESP32 3.3.x (TinyUSB 0.2x, ESP-IDF 5.5).
 */

#include "Arduino.h"
#include "sdkconfig.h"

#if !CONFIG_IDF_TARGET_ESP32S3
#error "Dieser Sketch ist nur fuer den ESP32-S3 (Tools > Board > ESP32S3 Dev Module)."
#endif
#if defined(ARDUINO_USB_MODE) && (ARDUINO_USB_MODE == 1)
#error "Tools > USB Mode muss 'USB-OTG (TinyUSB)' sein (nicht 'Hardware CDC and JTAG')."
#endif
#if ARDUINO_USB_CDC_ON_BOOT
#error "Tools > USB CDC On Boot muss 'Disabled' sein (die USB-Schnittstelle gehoert dem Bluetooth-Adapter)."
#endif
#if !CONFIG_BT_ENABLED
#error "Bluetooth ist in diesem Arduino-Core-Build deaktiviert."
#endif

#include "USB.h"
#include "esp_bt.h"
#include "tusb.h"  // tud_*()-Funktionen, Typen (explizit noetig, USB.h bindet es nicht ein)
#include "device/usbd_pvt.h"

// ======================= Konfiguration =======================
#define BT_USB_VID 0x1209  // pid.codes Test-VID/PID (nur fuer private/Test-Zwecke, frei aenderbar)
#define BT_USB_PID 0x0001
#define BT_USB_MANUFACTURER "ESP32-S3 DIY"
#define BT_USB_PRODUCT "ESP32-S3 Bluetooth Dongle (BLE)"
#define SERIAL_BAUD 115200
#define HCI_TRACE 1  // 0 = aus, 1 = HCI-Kommandos + Command Complete/Status + Verbindungs-Events, 2 = alle Events

// ======================= Konstanten =======================
#define HCI_PKT_CAP 520     // max. Paketgroesse inkl. H4-Typbyte (Controller-ACL: 251 + 4 + 1)
#define H2C_SLOTS 24        // Puffer Host -> Controller
#define C2H_SLOTS 32        // Puffer Controller -> Host
#define HCI_CMD_MAX 260     // 3 Byte Header + 255 Byte Parameter (+ Reserve)
#define BT_BULK_MPS 64      // Full-Speed Bulk-Paketgroesse
#define BT_RHPORT 0

#define H4_CMD 0x01
#define H4_ACL 0x02
#define H4_SCO 0x03
#define H4_EVT 0x04

static const uint8_t EP_EVT_IN = 0x81;   // Interrupt IN: HCI-Events
static const uint8_t EP_ACL_OUT = 0x02;  // Bulk OUT:     ACL Host -> Controller
static const uint8_t EP_ACL_IN = 0x82;   // Bulk IN:      ACL Controller -> Host

// ======================= Typen =======================
struct HciPkt {
  uint16_t len;  // Gesamtlaenge inkl. H4-Typbyte in data[0]
  uint8_t data[HCI_PKT_CAP];
};

struct Stats {  // nur Informationszaehler (nicht atomar, reicht fuer die Statusausgabe)
  uint32_t cmds, aclOut, events, aclIn;
  uint32_t h2cDrop, c2hDrop, usbDrop, oversize, framing, sendTimeout;
};

struct OpName {
  uint16_t op;
  const char *name;
};

// ======================= Globale Daten =======================
static HciPkt g_h2c[H2C_SLOTS];
static HciPkt g_c2h[C2H_SLOTS];
static HciPkt g_h2cScratch;  // Ablage fuer Pakete, die mangels freiem Slot verworfen werden
static QueueHandle_t g_h2cFree, g_h2cUsed, g_c2hFree, g_c2hUsed;
static SemaphoreHandle_t g_sendAvail, g_evtDone, g_aclDone;
static Stats g_stat;

static volatile bool g_usbCfg = false;  // Host hat die Konfiguration gewaehlt
static uint8_t g_altIso = 0;            // aktuelles Alt-Setting von Interface 1 (nur Buchfuehrung)

static uint8_t g_cmdBuf[HCI_CMD_MAX] __attribute__((aligned(4)));
static uint8_t g_aclRx[BT_BULK_MPS] __attribute__((aligned(4)));
static uint8_t g_evtTx[HCI_PKT_CAP] __attribute__((aligned(4)));
static uint8_t g_aclTx[HCI_PKT_CAP] __attribute__((aligned(4)));

// Zustand des ACL-Empfangs (nur im USB-Task benutzt)
static HciPkt *g_rxPkt = nullptr;
static uint8_t g_rxIdx = 0;
static bool g_rxDiscard = false;
static uint16_t g_rxHave = 0, g_rxNeed = 0;

// Nur fuer die Trace-Ausgabe: Opcode = (OGF << 10) | OCF. Unbekannte Opcodes werden als "?" angezeigt.
static const OpName kOps[] = {
  { 0x0401, "Inquiry (Classic)" }, { 0x0406, "Disconnect" }, { 0x0C01, "Set Event Mask" }, { 0x0C03, "Reset" },
  { 0x0C05, "Set Event Filter" }, { 0x0C13, "Write Local Name" }, { 0x0C14, "Read Local Name" },
  { 0x0C1A, "Write Scan Enable (Classic)" }, { 0x0C23, "Read Class of Device" }, { 0x0C24, "Write Class of Device" },
  { 0x0C25, "Read Voice Setting" }, { 0x0C2D, "Read Transmit Power Level" },
  { 0x0C31, "Set Controller To Host Flow Control" }, { 0x0C33, "Host Buffer Size" },
  { 0x0C35, "Host Number Of Completed Packets" }, { 0x0C56, "Write Simple Pairing Mode" },
  { 0x0C63, "Set Event Mask Page 2" }, { 0x0C6C, "Read LE Host Support" }, { 0x0C6D, "Write LE Host Support" },
  { 0x1001, "Read Local Version Information" }, { 0x1002, "Read Local Supported Commands" },
  { 0x1003, "Read Local Supported Features" }, { 0x1004, "Read Local Extended Features" },
  { 0x1005, "Read Buffer Size (Classic)" }, { 0x1009, "Read BD_ADDR" },
  { 0x2001, "LE Set Event Mask" }, { 0x2002, "LE Read Buffer Size" }, { 0x2003, "LE Read Local Supported Features" },
  { 0x2005, "LE Set Random Address" }, { 0x2006, "LE Set Advertising Parameters" }, { 0x2008, "LE Set Advertising Data" },
  { 0x200A, "LE Set Advertising Enable" }, { 0x200B, "LE Set Scan Parameters" }, { 0x200C, "LE Set Scan Enable" },
  { 0x200D, "LE Create Connection" }, { 0x200E, "LE Create Connection Cancel" },
  { 0x200F, "LE Read Filter Accept List Size" }, { 0x2010, "LE Clear Filter Accept List" },
  { 0x2011, "LE Add Device To Filter Accept List" }, { 0x2013, "LE Connection Update" },
  { 0x2017, "LE Encrypt" }, { 0x2018, "LE Rand" }, { 0x2019, "LE Enable Encryption" },
  { 0x201C, "LE Read Supported States" }, { 0x2022, "LE Set Data Length" },
  { 0x2023, "LE Read Suggested Default Data Length" }, { 0x2024, "LE Write Suggested Default Data Length" },
  { 0x202E, "LE Set Resolvable Private Address Timeout" }, { 0x202F, "LE Read Maximum Data Length" },
  { 0x2031, "LE Set Default PHY" }, { 0x2032, "LE Set PHY" },
  { 0x2041, "LE Set Extended Scan Parameters" }, { 0x2042, "LE Set Extended Scan Enable" },
  { 0x2043, "LE Extended Create Connection" }, { 0x204B, "LE Read Transmit Power" },
};

// ======================= Hilfsfunktionen =======================
// Queue-/Semaphore-Zugriffe, die sowohl aus Tasks als auch (falls noetig) aus dem ISR-Kontext funktionieren.
static bool qGet(QueueHandle_t q, uint8_t *idx, TickType_t wait) {
  if (xPortInIsrContext()) {
    BaseType_t woken = pdFALSE;
    bool ok = (xQueueReceiveFromISR(q, idx, &woken) == pdTRUE);
    if (woken == pdTRUE) portYIELD_FROM_ISR();
    return ok;
  }
  return xQueueReceive(q, idx, wait) == pdTRUE;
}

static bool qPut(QueueHandle_t q, uint8_t idx) {
  if (xPortInIsrContext()) {
    BaseType_t woken = pdFALSE;
    bool ok = (xQueueSendFromISR(q, &idx, &woken) == pdTRUE);
    if (woken == pdTRUE) portYIELD_FROM_ISR();
    return ok;
  }
  return xQueueSend(q, &idx, 0) == pdTRUE;
}

static void semGive(SemaphoreHandle_t s) {
  if (xPortInIsrContext()) {
    BaseType_t woken = pdFALSE;
    xSemaphoreGiveFromISR(s, &woken);
    if (woken == pdTRUE) portYIELD_FROM_ISR();
  } else {
    xSemaphoreGive(s);
  }
}

// usbd_edpt_xfer() hat in aelteren TinyUSB-Versionen 4, in neueren 5 Parameter (is_isr).
// Die Ueberladung waehlt zur Compile-Zeit die passende Variante.
static bool xferVia(bool (*f)(uint8_t, uint8_t, uint8_t *, uint16_t), uint8_t ep, uint8_t *buf, uint16_t len) {
  return f(BT_RHPORT, ep, buf, len);
}
static bool xferVia(bool (*f)(uint8_t, uint8_t, uint8_t *, uint16_t, bool), uint8_t ep, uint8_t *buf, uint16_t len) {
  return f(BT_RHPORT, ep, buf, len, false);
}

static const char *opName(uint16_t op) {
  for (size_t i = 0; i < sizeof(kOps) / sizeof(kOps[0]); i++) {
    if (kOps[i].op == op) return kOps[i].name;
  }
  return "?";
}

static void fatal(const char *msg) {
  for (;;) {
    Serial.printf("FEHLER: %s\n", msg);
    Serial.println("Status: NICHT bereit (Neustart/Reset noetig)");
    delay(3000);
  }
}

// ======================= Trace (Serial-Monitor) =======================
static void traceHostPacket(const HciPkt &p) {
#if HCI_TRACE >= 1
  if (p.data[0] == H4_CMD && p.len >= 4) {
    uint16_t op = (uint16_t)(p.data[1] | (p.data[2] << 8));
    Serial.printf("[HCI] Windows -> Controller: Kommando 0x%04X %s (%u Byte Parameter)\n", op, opName(op), p.data[3]);
  }
#endif
}

static void traceControllerPacket(const uint8_t *pl, uint16_t n, uint8_t type) {
#if HCI_TRACE >= 1
  if (type != H4_EVT || n < 2) return;
  const uint8_t code = pl[0];
  if (code == 0x0E && n >= 6) {  // Command Complete
    uint16_t op = (uint16_t)(pl[3] | (pl[4] << 8));
    Serial.printf("[HCI] Controller -> Windows: Command Complete 0x%04X %s, Status 0x%02X%s\n", op, opName(op), pl[5],
                  pl[5] == 0x01 ? " (Unknown HCI Command)" : "");
    return;
  }
  if (code == 0x0F && n >= 6) {  // Command Status
    uint16_t op = (uint16_t)(pl[4] | (pl[5] << 8));
    Serial.printf("[HCI] Controller -> Windows: Command Status 0x%04X %s, Status 0x%02X\n", op, opName(op), pl[2]);
    return;
  }
  if (code == 0x05 && n >= 6) {  // Disconnection Complete
    Serial.printf("[HCI] Controller -> Windows: Disconnection Complete, Status 0x%02X, Grund 0x%02X\n", pl[2], pl[5]);
    return;
  }
  if (code == 0x3E && n >= 4 && (pl[2] == 0x01 || pl[2] == 0x0A)) {  // LE (Enhanced) Connection Complete
    Serial.printf("[HCI] Controller -> Windows: LE Connection Complete, Status 0x%02X\n", pl[3]);
    return;
  }
#if HCI_TRACE >= 2
  Serial.printf("[HCI] Controller -> Windows: Event 0x%02X (%u Byte)\n", code, n);
#endif
#else
  (void)pl;
  (void)n;
  (void)type;
#endif
}

// ======================= VHCI-Bruecke (Controller-Seite) =======================
// Wird vom Bluetooth-Controller aufgerufen, wenn er ein HCI-Paket (mit H4-Typbyte) fuer den Host hat.
// Die Daten sind nur waehrend des Aufrufs gueltig und werden deshalb kopiert.
static int onControllerPacket(uint8_t *data, uint16_t len) {
  if (len < 2) return 0;
  if (len > HCI_PKT_CAP) {
    g_stat.oversize++;
    return 0;
  }
  if (!g_usbCfg) {  // kein konfigurierter Host: nicht puffern, den Controller nicht ausbremsen
    g_stat.usbDrop++;
    return 0;
  }
  uint8_t idx;
  if (!qGet(g_c2hFree, &idx, pdMS_TO_TICKS(50))) {  // kurzer Rueckstau, sonst verwerfen
    g_stat.c2hDrop++;
    return 0;
  }
  memcpy(g_c2h[idx].data, data, len);
  g_c2h[idx].len = len;
  qPut(g_c2hUsed, idx);
  return 0;
}

static void onSendAvailable(void) {
  semGive(g_sendAvail);
}

static const esp_vhci_host_callback_t g_vhciCb = { onSendAvailable, onControllerPacket };

// ======================= Task: Windows -> Controller =======================
static void h2cTask(void *arg) {
  (void)arg;
  for (;;) {
    uint8_t idx;
    if (xQueueReceive(g_h2cUsed, &idx, portMAX_DELAY) != pdTRUE) continue;
    HciPkt &p = g_h2c[idx];
    traceHostPacket(p);

    bool sent = false;
    uint32_t t0 = millis();
    while (millis() - t0 < 2000) {
      if (esp_vhci_host_check_send_available()) {
        esp_vhci_host_send_packet(p.data, p.len);
        sent = true;
        break;
      }
      xSemaphoreTake(g_sendAvail, pdMS_TO_TICKS(10));
    }
    if (sent) {
      if (p.data[0] == H4_CMD) g_stat.cmds++;
      else g_stat.aclOut++;
    } else {
      g_stat.sendTimeout++;
      Serial.println("[HCI] WARNUNG: Controller nahm Paket nicht an (Timeout), Paket verworfen");
    }
    qPut(g_h2cFree, idx);
  }
}

// ======================= USB-Senderichtung (Task: Controller -> Windows) =======================
static bool epSendOne(uint8_t ep, SemaphoreHandle_t done, uint8_t *buf, uint16_t len) {
  uint32_t t0 = millis();
  while (!usbd_edpt_claim(BT_RHPORT, ep)) {
    if (!g_usbCfg || millis() - t0 > 200) return false;
    vTaskDelay(1);
  }
  xSemaphoreTake(done, 0);  // alte Signale verwerfen
  if (!xferVia(usbd_edpt_xfer, ep, buf, len)) {
    usbd_edpt_release(BT_RHPORT, ep);
    return false;
  }
  t0 = millis();
  while (xSemaphoreTake(done, pdMS_TO_TICKS(20)) != pdTRUE) {
    if (!g_usbCfg || millis() - t0 > 1000) return false;
  }
  return true;
}

// Bulk-IN: Ist die Laenge ein Vielfaches der Paketgroesse, muss ein Zero-Length-Packet das Ende markieren.
static bool epSend(uint8_t ep, SemaphoreHandle_t done, uint8_t *buf, uint16_t len, bool zlp) {
  if (!epSendOne(ep, done, buf, len)) return false;
  if (zlp && len > 0 && (len % BT_BULK_MPS) == 0) return epSendOne(ep, done, buf, 0);
  return true;
}

static void c2hTask(void *arg) {
  (void)arg;
  for (;;) {
    uint8_t idx;
    if (xQueueReceive(g_c2hUsed, &idx, portMAX_DELAY) != pdTRUE) continue;
    HciPkt &p = g_c2h[idx];
    const uint8_t type = p.data[0];
    const uint16_t n = (uint16_t)(p.len - 1);
    traceControllerPacket(&p.data[1], n, type);

    bool ok = false;
    if (g_usbCfg && !tud_suspended()) {
      if (type == H4_EVT) {
        memcpy(g_evtTx, &p.data[1], n);
        ok = epSend(EP_EVT_IN, g_evtDone, g_evtTx, n, false);
        if (ok) g_stat.events++;
      } else if (type == H4_ACL) {
        memcpy(g_aclTx, &p.data[1], n);
        ok = epSend(EP_ACL_IN, g_aclDone, g_aclTx, n, true);
        if (ok) g_stat.aclIn++;
      }
      // H4_SCO / ISO: vom LE-Controller nicht erzeugt, ein solches Paket wird verworfen.
    }
    if (!ok) g_stat.usbDrop++;
    qPut(g_c2hFree, idx);
  }
}

// ======================= USB-Descriptors =======================
// Device-Descriptor: Klasse 0xE0 (Wireless Controller), Subklasse 0x01 (RF), Protokoll 0x01 (Bluetooth).
// Windows bindet darueber ueber die Compatible-ID USB\Class_E0&SubClass_01&Prot_01 den Inbox-Treiber bthusb.
static const uint8_t kDeviceDesc[18] __attribute__((aligned(4))) = {
  18, 0x01,                                  // bLength, bDescriptorType (Device)
  0x00, 0x02,                                // bcdUSB 2.00
  0xE0, 0x01, 0x01,                          // Bluetooth Primary Controller
  64,                                        // bMaxPacketSize0
  BT_USB_VID & 0xFF, (BT_USB_VID >> 8) & 0xFF,
  BT_USB_PID & 0xFF, (BT_USB_PID >> 8) & 0xFF,
  0x00, 0x01,                                // bcdDevice 1.00
  1, 2, 3,                                   // iManufacturer, iProduct, iSerialNumber
  1                                          // bNumConfigurations
};

// SCO-Alt-Setting (Interface 1): zwei Isochronous-Endpoints, wie bei marktueblichen Bluetooth-Dongles.
#define ISO_ALT(alt, sz)                                           \
  9, 0x04, 1, (alt), 2, 0xE0, 0x01, 0x01, 0,                       \
  7, 0x05, 0x83, 0x01, (sz), 0x00, 1,                              \
  7, 0x05, 0x03, 0x01, (sz), 0x00, 1

static const uint8_t kConfigDesc[] __attribute__((aligned(4))) = {
  // Konfiguration: 2 Interfaces, bus-powered, 500 mA
  9, 0x02, 177, 0x00, 2, 1, 0, 0x80, 250,
  // Interface 0: HCI (Kommandos ueber EP0, Events, ACL)
  9, 0x04, 0, 0, 3, 0xE0, 0x01, 0x01, 0,
  7, 0x05, 0x81, 0x03, 64, 0x00, 1,  // Interrupt IN  (HCI-Events)
  7, 0x05, 0x02, 0x02, 64, 0x00, 0,  // Bulk OUT      (ACL Host -> Controller)
  7, 0x05, 0x82, 0x02, 64, 0x00, 0,  // Bulk IN       (ACL Controller -> Host)
  // Interface 1: Isochronous (SCO), Alt-Settings 0..5 mit 0/9/17/25/33/49 Byte
  ISO_ALT(0, 0), ISO_ALT(1, 9), ISO_ALT(2, 17), ISO_ALT(3, 25), ISO_ALT(4, 33), ISO_ALT(5, 49)
};
static_assert(sizeof(kConfigDesc) == 177, "wTotalLength der Konfiguration stimmt nicht");

static char g_serialStr[17];

// Die Callbacks stehen in einem extern-"C"-Block (einzelne extern-"C"-Definitionen bringen den Prototyp-Generator
// der Arduino IDE durcheinander). Ihre Deklarationen stammen aus tusb.h, sie ersetzen die weak-Versionen des Cores.
extern "C" {

const uint8_t *tud_descriptor_device_cb(void) {
  return kDeviceDesc;
}

const uint8_t *tud_descriptor_configuration_cb(uint8_t index) {
  (void)index;
  return kConfigDesc;
}

const uint16_t *tud_descriptor_string_cb(uint8_t index, uint16_t langid) {
  (void)langid;
  static uint16_t desc[40];
  const char *s = nullptr;
  uint8_t count;
  if (index == 0) {
    desc[1] = 0x0409;  // Englisch (US)
    count = 1;
  } else {
    if (index == 1) s = BT_USB_MANUFACTURER;
    else if (index == 2) s = BT_USB_PRODUCT;
    else if (index == 3) s = g_serialStr;
    else return nullptr;  // u.a. Microsoft-OS-Descriptor (0xEE): nicht vorhanden
    count = (uint8_t)strlen(s);
    if (count > 38) count = 38;
    for (uint8_t i = 0; i < count; i++) desc[1 + i] = (uint16_t)s[i];
  }
  desc[0] = (uint16_t)((0x03 << 8) | (2 * count + 2));
  return desc;
}

}  // extern "C"

// ======================= USB-Klassentreiber "Bluetooth HCI" =======================
// Eigener TinyUSB-Treiber (der Arduino-Core hat keinen Bluetooth-Klassentreiber).
static void btdInit(void) {}

static void rxDropCurrent(void) {
  if (g_rxPkt != nullptr && g_rxPkt != &g_h2cScratch) qPut(g_h2cFree, g_rxIdx);
  g_rxPkt = nullptr;
}

static void btdReset(uint8_t rhport) {
  (void)rhport;
  g_usbCfg = false;
  g_altIso = 0;
  rxDropCurrent();
}

static uint16_t btdOpen(uint8_t rhport, tusb_desc_interface_t const *itf, uint16_t maxLen) {
  const uint16_t total = (uint16_t)(sizeof(kConfigDesc) - 9);  // beide Interfaces inkl. Alt-Settings
  if (itf->bInterfaceClass != 0xE0 || itf->bInterfaceSubClass != 0x01 || itf->bInterfaceProtocol != 0x01) return 0;
  if (itf->bInterfaceNumber != 0 || itf->bNumEndpoints != 3 || maxLen < total) return 0;

  const uint8_t *p = (const uint8_t *)itf;
  p += p[0];  // hinter den Interface-Descriptor, auf den ersten Endpoint
  for (int i = 0; i < 3; i++) {
    if (p[1] != 0x05) return 0;
    if (!usbd_edpt_open(rhport, (tusb_desc_endpoint_t const *)p)) return 0;
    p += p[0];
  }
  rxDropCurrent();
  if (!xferVia(usbd_edpt_xfer, EP_ACL_OUT, g_aclRx, BT_BULK_MPS)) return 0;  // Empfang der ACL-Daten starten
  g_usbCfg = true;
  return total;
}

// ACL-Daten vom Host kommen in Stuecken von je einem USB-Paket (<= 64 Byte). Das HCI-ACL-Paket wird
// anhand des Laengenfeldes im ACL-Header zusammengesetzt, egal ob der Host ein Zero-Length-Packet sendet.
static void aclRxChunk(const uint8_t *d, uint16_t n) {
  if (n == 0) return;
  if (g_rxPkt == nullptr) {
    uint8_t idx;
    if (qGet(g_h2cFree, &idx, 0)) {
      g_rxIdx = idx;
      g_rxPkt = &g_h2c[idx];
      g_rxDiscard = false;
    } else {
      g_rxPkt = &g_h2cScratch;
      g_rxDiscard = true;
      g_stat.h2cDrop++;
    }
    g_rxPkt->data[0] = H4_ACL;
    g_rxHave = 0;
    g_rxNeed = 0;
  }
  if ((uint32_t)1 + g_rxHave + n <= HCI_PKT_CAP) memcpy(&g_rxPkt->data[1 + g_rxHave], d, n);
  else g_rxDiscard = true;
  g_rxHave = (uint16_t)(g_rxHave + n);

  if (g_rxNeed == 0 && g_rxHave >= 4) g_rxNeed = (uint16_t)(4 + (g_rxPkt->data[3] | (g_rxPkt->data[4] << 8)));

  const bool complete = (g_rxNeed != 0 && g_rxHave >= g_rxNeed);
  const bool truncated = (n < BT_BULK_MPS && !complete);  // kurzes Paket, aber ACL-Laenge nicht erreicht
  if (!complete && !truncated) return;

  if (truncated) g_stat.framing++;
  if (complete && !g_rxDiscard) {
    g_rxPkt->len = (uint16_t)(1 + g_rxNeed);
    qPut(g_h2cUsed, g_rxIdx);
  } else {
    rxDropCurrent();
  }
  g_rxPkt = nullptr;
}

static bool btdXfer(uint8_t rhport, uint8_t ep, xfer_result_t result, uint32_t n) {
  (void)rhport;
  if (ep == EP_ACL_OUT) {
    if (result == XFER_RESULT_SUCCESS) aclRxChunk(g_aclRx, (uint16_t)n);
    if (g_usbCfg) xferVia(usbd_edpt_xfer, EP_ACL_OUT, g_aclRx, BT_BULK_MPS);
  } else if (ep == EP_EVT_IN) {
    semGive(g_evtDone);
  } else if (ep == EP_ACL_IN) {
    semGive(g_aclDone);
  }
  return true;
}

static bool btdControl(uint8_t rhport, uint8_t stage, tusb_control_request_t const *req) {
  const uint8_t type = req->bmRequestType_bit.type;

  if (type == TUSB_REQ_TYPE_CLASS) {
    // HCI-Kommando: Class-Request, bRequest 0 (historisch 0xE0), wValue 0, Daten-Richtung Host -> Geraet.
    if (req->bRequest != 0x00 && req->bRequest != 0xE0) return false;
    if (req->bmRequestType_bit.direction != TUSB_DIR_OUT) return false;
    if (stage == CONTROL_STAGE_SETUP) {
      if (req->wLength < 3 || req->wLength > sizeof(g_cmdBuf)) return false;
      return tud_control_xfer(rhport, req, g_cmdBuf, req->wLength);
    }
    if (stage == CONTROL_STAGE_DATA) {  // Kommando vollstaendig empfangen
      uint8_t idx;
      if (!qGet(g_h2cFree, &idx, 0)) {
        g_stat.h2cDrop++;
        return false;
      }
      g_h2c[idx].data[0] = H4_CMD;
      memcpy(&g_h2c[idx].data[1], g_cmdBuf, req->wLength);
      g_h2c[idx].len = (uint16_t)(1 + req->wLength);
      qPut(g_h2cUsed, idx);
    }
    return true;
  }

  if (type == TUSB_REQ_TYPE_STANDARD && req->bmRequestType_bit.recipient == TUSB_REQ_RCPT_INTERFACE) {
    if (stage != CONTROL_STAGE_SETUP) return true;
    const uint8_t itfNum = (uint8_t)(req->wIndex & 0xFF);
    if (req->bRequest == TUSB_REQ_SET_INTERFACE) {
      const uint8_t alt = (uint8_t)(req->wValue & 0xFF);
      // Interface 0 kennt nur Alt 0. Interface 1 (SCO) wird angenommen, seine Endpoints bleiben aber geschlossen.
      if ((itfNum == 0 && alt == 0) || (itfNum == 1 && alt <= 5)) {
        if (itfNum == 1) g_altIso = alt;
        return tud_control_status(rhport, req);
      }
      return false;
    }
    if (req->bRequest == TUSB_REQ_GET_INTERFACE) {
      uint8_t alt = (itfNum == 1) ? g_altIso : 0;
      return tud_control_xfer(rhport, req, &alt, 1);
    }
  }
  return false;
}

static usbd_class_driver_t g_btDriver;

extern "C" {

const usbd_class_driver_t *usbd_app_driver_get_cb(uint8_t *driver_count) {
  memset(&g_btDriver, 0, sizeof(g_btDriver));
  g_btDriver.init = btdInit;
  g_btDriver.reset = btdReset;
  g_btDriver.open = btdOpen;
  g_btDriver.control_xfer_cb = btdControl;
  g_btDriver.xfer_cb = btdXfer;
  *driver_count = 1;
  return &g_btDriver;
}

}  // extern "C"

// ======================= Verhindert Freigabe des BLE-Speichers =======================
// Der Arduino-Core gibt beim Start den Bluetooth-Speicher frei, wenn kein BLE-Sketch erkannt wird.
bool btInUse() {
  return true;
}
bool bleInUse() {
  return true;
}

// ======================= Initialisierung =======================
static bool createObjects(void) {
  g_h2cFree = xQueueCreate(H2C_SLOTS, sizeof(uint8_t));
  g_h2cUsed = xQueueCreate(H2C_SLOTS, sizeof(uint8_t));
  g_c2hFree = xQueueCreate(C2H_SLOTS, sizeof(uint8_t));
  g_c2hUsed = xQueueCreate(C2H_SLOTS, sizeof(uint8_t));
  g_sendAvail = xSemaphoreCreateBinary();
  g_evtDone = xSemaphoreCreateBinary();
  g_aclDone = xSemaphoreCreateBinary();
  if (!g_h2cFree || !g_h2cUsed || !g_c2hFree || !g_c2hUsed || !g_sendAvail || !g_evtDone || !g_aclDone) return false;
  for (uint8_t i = 0; i < H2C_SLOTS; i++) xQueueSend(g_h2cFree, &i, 0);
  for (uint8_t i = 0; i < C2H_SLOTS; i++) xQueueSend(g_c2hFree, &i, 0);
  return true;
}

static void printStatus(void) {
  Serial.printf("[Status] USB: %s | HCI-Kommandos: %lu | Events: %lu | ACL Windows->BLE: %lu | ACL BLE->Windows: %lu\n",
                tud_mounted() ? (tud_suspended() ? "suspendiert" : "konfiguriert") : "nicht konfiguriert",
                (unsigned long)g_stat.cmds, (unsigned long)g_stat.events, (unsigned long)g_stat.aclOut,
                (unsigned long)g_stat.aclIn);
  if (g_stat.h2cDrop || g_stat.c2hDrop || g_stat.usbDrop || g_stat.oversize || g_stat.framing || g_stat.sendTimeout) {
    Serial.printf("[Status] verworfen: H2C=%lu C2H=%lu USB=%lu zu gross=%lu Framing=%lu Sende-Timeout=%lu\n",
                  (unsigned long)g_stat.h2cDrop, (unsigned long)g_stat.c2hDrop, (unsigned long)g_stat.usbDrop,
                  (unsigned long)g_stat.oversize, (unsigned long)g_stat.framing, (unsigned long)g_stat.sendTimeout);
  }
}

void setup() {
  Serial.begin(SERIAL_BAUD);
  delay(500);
  Serial.println();
  Serial.println("ESP32-S3 Bluetooth USB Dongle");
#ifdef ESP_ARDUINO_VERSION_MAJOR
  Serial.printf("Arduino-ESP32 %d.%d.%d, ESP-IDF %s\n", ESP_ARDUINO_VERSION_MAJOR, ESP_ARDUINO_VERSION_MINOR,
                ESP_ARDUINO_VERSION_PATCH, ESP.getSdkVersion());
#endif
#ifdef TUSB_VERSION_STRING
  Serial.printf("TinyUSB %s\n", TUSB_VERSION_STRING);
#endif
  Serial.println("Hinweis: ESP32-S3 = nur Bluetooth LE (kein Bluetooth Classic)");

  snprintf(g_serialStr, sizeof(g_serialStr), "%012llX", (unsigned long long)ESP.getEfuseMac());

  if (!createObjects()) fatal("Speicher fuer Warteschlangen/Semaphoren fehlt");

  // 1. Bluetooth-Controller (BLE) starten
  if (!btStart()) {
    fatal("Bluetooth-Controller konnte nicht gestartet werden (btStart). "
          "Pruefen: USB Mode/Core-Version, genug freier Speicher, BT-Speicher nicht freigegeben");
  }
  if (esp_bt_controller_get_status() != ESP_BT_CONTROLLER_STATUS_ENABLED) fatal("Bluetooth-Controller ist nicht im Status ENABLED");
  Serial.println("Bluetooth initialisiert (BLE-Controller aktiv)");

  // 2. HCI-Bruecke (VHCI) und Transport-Tasks
  esp_err_t err = esp_vhci_host_register_callback(&g_vhciCb);
  if (err != ESP_OK) {
    Serial.printf("esp_vhci_host_register_callback: %s\n", esp_err_to_name(err));
    fatal("VHCI-Callback konnte nicht registriert werden");
  }
  if (xTaskCreatePinnedToCore(h2cTask, "hci_h2c", 4096, nullptr, 15, nullptr, 1) != pdPASS ||
      xTaskCreatePinnedToCore(c2hTask, "hci_c2h", 4096, nullptr, 15, nullptr, 1) != pdPASS) {
    fatal("HCI-Tasks konnten nicht gestartet werden");
  }
  Serial.println("HCI initialisiert (VHCI-Bruecke aktiv)");

  // 3. USB zuletzt starten: Windows sendet sofort HCI_Reset, die Bruecke muss dann bereitstehen
  if (!USB.begin()) fatal("USB.begin() fehlgeschlagen (TinyUSB nicht gestartet)");
  Serial.printf("USB initialisiert (VID:PID %04X:%04X, Klasse 0xE0/0x01/0x01 = Bluetooth-Adapter, Seriennr. %s)\n",
                BT_USB_VID, BT_USB_PID, g_serialStr);
  Serial.println("Status: bereit");
  Serial.println("Windows-Anschluss: USB-Buchse (nativ). Serial-Monitor: UART-Buchse.");
}

void loop() {
  static uint32_t lastStatus = 0;
  static bool lastCfg = false;
  static bool warned = false;

  if (g_usbCfg != lastCfg) {
    lastCfg = g_usbCfg;
    Serial.println(lastCfg ? "[USB] Windows hat die Bluetooth-Konfiguration gewaehlt (Geraet konfiguriert)"
                           : "[USB] Konfiguration beendet (Kabel gezogen, Bus-Reset oder Standby)");
  }
  if (!warned && !g_usbCfg && millis() > 15000) {
    warned = true;
    Serial.println("[USB] Noch kein Host verbunden/konfiguriert. USB-Kabel in der NATIVEN 'USB'-Buchse? "
                   "Geraete-Manager auf 'Unbekanntes USB-Geraet' pruefen.");
  }
  if (millis() - lastStatus >= 10000) {
    lastStatus = millis();
    printStatus();
  }
  delay(50);
}
