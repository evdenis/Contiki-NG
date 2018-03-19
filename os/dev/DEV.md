# Devices drivers

## GPIO-HAL

### Dependencies:

- LIB/LIST

### Verification status:

- no verification attempted
- requires \valid_function

## LEDS

### Dependencies:

- architecture
- GPIO

### Verification status:

- no verification attempted
- some bit manipulation
- requires contracts for GPIO

## NULLRADIO

Not relevant (but should be trivial)

## SERIAL-LINE

### Dependencies:

- SYS/PROCESS
- LIB/RINGBUF

### Verification status:

- no verification attempted
- non-natural loops

## SLIP

### Dependencies:

- NET/IPV6/UIP <-- why ?
- PROCESS
- architecture

### Verification status:

- no verification attempted
- requires \valid_function

## Macros and external APIs

 - BATTERY-SENSOR
 - BLE-HAL
 - BUTTON-SENSOR
 - EEPROM
 - ROM
 - SPI
 - WATCHDOG
 - XMEM