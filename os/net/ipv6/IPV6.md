# IPV6 Module

## IP64-ADDR:

- no verification attempted
- should be easy to verify for absence of RTE
- functional verification requires a bit of formalization for IP

## PSOCK:

- no verification attempted
- some functions should be easy to verify for absence of RTE
- rely on protothread
    - non-natural loops (Conc2Seq ?)
- functional verification could be hard

## RESOLV:

- no verification attempted
- probably quite hard to verify:
    - global variables
    - gotos
    - long functions with a lot of flags and constant
    - rely on protothread
    - direct calls to the scheduler (probably a bad idea)

## SICSLOWPAN:

- absence of RTE started by Quentin Molle
- quite hard to verify:
   - globals variables
   - long functions with flags and constants
   - unions

## SIMPLE-UDP:

- no verification attempted
- rely on UIP
- rely on protothread
- except for this, the code is quite simple

## TCPIP:

- no verification attempted
- code is not so complex but some part a bit messy
- rely on protothread
- rely on some kind of allocation/deallocation
    - could be a problem for WP

## TCP-SOCKET:

- no verification attempted
- could be hard to verify
    - rely on protothread
    - rely on LIST
    - some callback functions
    - talk with the scheduler

## UDP-SOCKET:

- no verification attempted
- rely on protothread
- except for this, the code is not too complex

## UIP6:

- no verification attempted
- does bad things with pointers and types
- a lot of global variables
- long functions
- gotos inside switches inside loops,
  with MACROS to deactivate parts of the code
- (no complex operations but bad ones)
- talk with timers
- uip_process in 1400 LOC long (have fun)

## UIPBUF:

- no verification attempted
- not too complex, just a single global to consider

## UIP-DEBUG:

- irrelevant for verification

## UIP-DS6:

- no verification attempted
- bad things with casts
- some kind of list but does not use the list API
- except for this the code is quite clean

## UIP-DS6-NBR:

- no verification attempted
- some global variables
- the code is quite clean but some part can be a bit tough to analyse

## UIP-DS6-ROUTE:

- no verification attempted
- rely (heavily) on LIST and MEMB
- some functions are quite long

## UIP-ICMP6:

- no verification attempted
- bad things with casts
- rely on LIST
- not so complex but relies on complex specifications

## UIPLIB:

- no verification attempted
- should be quite easy to verify for absence of RTE
- needs specification from IP64 however

## UIP-NAMESERVER:

- no verification attempted
- rely on LIST and MEMB
- the code is not too complex but spec could be

## UIP-ND6:

- no verification attempted
- a lot of global variables
- long functions with gotos
- bad things with casts

## UIP-PACKETQUEUE:

- no verification attempted
- rely on MEMB and timers
- except for this the code is quite simple

## UIP-SR:

- no verification attempted
- rely on LIST and MEMB
- the code is not too complex but spec could be

## UIP-UDP-PACKET:

- no verification attempted
- should not be too hard

## Macros or extern APIs libs :

- UIP-ARCH
- UIPOPT