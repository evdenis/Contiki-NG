# Core Netstack modules

## LINKADDR

### Dependencies:

- None

### Verification status:

- no verification attempted
- Absence of RTE should be trivial

## LINK-STATS

### Dependencies:

- SYS/CLOCK
- NET/PACKETBUF
- NET/NBR-TABLE

### Verification status:

- no verification attempted
- requires to have good specifications for NBR-TABLE and PACKETBUF
- many defines

## NBR-TABLE

### Dependencies:

- LIB/MEMB
- LIB/LIST
- NET/NBR-TABLE

### Verification status:

- no verification attempted
- global variables
- some pointer manipulation with casts
- a few functions are quite complex
- requires \valid_function

## NET-DEBUG

- no verification attempted
- verification probably not relevant

## NETSTACK

### Dependencies:

- LIB/LIST

### Verification status:

- no verification attempted
- requires \valid_function

## PACKETBUF

### Dependencies:

- SYS/CC 

### Verification status:

- no verification attempted
- some global variables
- some cast and pointer manipulation
- verification of absence of RTE would not be too hard

## QUEUEBUF

### Dependencies:

- (for DEBUG) LIB/LIST
- LIB/MEMB
- (Optionnaly) CFS

### Verification status:

- no verification attempted
- some global variables
- some code is activated/deactivated depending on macros

# Sub-modules

- [APP-LAYER](app-layer/APP-LAYER.md)
- [IPV6](ipv6/IPV6.md)
- [MAC](mac/MAC.md)
- [NULLNET](nullnet/NULLNET.md)
- [ROUTING](routing/ROUTING.md)
- [SECURITY](security/SECURITY.md)