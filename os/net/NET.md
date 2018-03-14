# Core Netstack modules

## LINKADDR

- no verification attempted
- Absence of RTE should be trivial

## LINK-STATS

- no verification attempted
- requires NBR-TABLE and PACKETBUF
    - requires to have good specifications for them
- many defines
- except for parts that communicate with NBR-TABLE and PACKETBUF
  it would not be too hard

## NBR-TABLE

- no verification attempted
- relies on MEMB and LIST modules
- global variables
- some pointer manipulation with casts
- a few functions are quite complex

## NET-DEBUG

- no verification attempted
- verification probably not relevant

## NETSTACK

- no verification attempted
- relies on LIST module
- except this, it would not be too hard

## PACKETBUF

- no verification attempted
- some global variables
- verification of absence of RTE would not be too hard

## QUEUEBUF

- no verification attempted
- uses a some kind of list for DEBUG, without using the LIST module
- relies on MEMB/CFS
- some global variables
- some code is activated/deactivated depending on macros

# Sub-modules

- [APP-LAYER](app-layer/APP-LAYER.md)
- [IPV6](ipv6/IPV6.md)
- [MAC](mac/MAC.md)
- [NULLNET](nullnet/NULLNET.md)
- [ROUTING](routing/ROUTING.md)
- [SECURITY](security/SECURITY.md)