# TSCH Protocol

## TSCH-ADAPTATIVE-TIME_SYNC

### Dependencies

- TSCH

### Verification status

- no verification attempted
- some global variables
- it does not seem too hard to verify but the invariant of
  the globals could be tricky

## TSCH

### Dependencies

- PROTOTHREAD
- PROCESS
- CTIMER
- TSCH-QUEUE
- TSCH-ASN
- TSCH-SCHEDULE
- NET/LINKADDR
- NET/NBR-TABLE
- NET/LINK-STATS
- NET/PACKETBUF

### Verification status

- no verification attempted
- a lot of global variables
- non-natural loops
- complex pieces of code

## TSCH-LOG

### Dependencies

- LIB/RINGBUFINDEX
- all other TSCH modules

### Verification status

- no verification attempted
- probably not so relevant for verification

## TSCH-PACKET

### Dependencies

- NET/PACKETBUF
- NET/LINKADDR
- NET/MAC/LLSEC802154

### Verification status

- no verification attempted
- calls to parsing functions
- lot of memory operations
- some long functions

## TSCH-QUEUE

### Dependencies

- LIB/LIST
- LIB/MEMB
- LIB/RINGBUFINDEX
- NET/LINKADDR

### Verification status

- no verification attempted
- some global variables
- contracts could be quite complex (due to dependencies)

## TSCH-RPL

### Dependencies

- TSCH
- NET/ROUTING

### Verification status

- no verification attempted
- the code is simple, however contracts of called function
  may not be simple

## TSCH-SCHEDULE

### Dependencies

- LIB/LIST
- LIB/MEMB
- TSCH
- NET/LINKADDR

### Verification status

- no verification attempted
- some function could be very complex to verify due to lists

## TSCH-SECURITY

### Dependencies

- NET/PACKETBUF
- NET/MAC/LLSEC802154
- LIB/AES-128
- LIB/CCM-STAR

### Verification status

- no verification attempted
- the code by itself is simple
- complexity will depend on the complexity of called function

## TSCH-SLOT-OPERATION

### Dependencies

- PROTOTHREAD
- TSCH-ASN
- TSCH-QUEUE
- TSCH-PACKET
- TSCH-SCHEDULE
- NET/QUEUEBUF
- SYS/RTIMER

### Verification status

- no verification attempted
- a lot of global variables
- some very long functions
- protothreads -> global invariants

## MACRO and headers for extern functions:

- TSCH-ASN
- TSCH-CONF
- TSCH-PRIVATE