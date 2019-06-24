# IPV6 Module

## IP64-ADDR:

### Dependencies:

- None

### Verification status:

- no verification attempted
- should be easy to verify for absence of RTE
- functional verification requires a bit of formalization for IP

## PSOCK:

### Dependencies:

- None

### Verification status:

- no verification attempted
- some functions should be easy to verify for absence of RTE
- rely on protothread
    - non-natural loops (Conc2Seq ?)
- requires \valid_function

## RESOLV:

### Dependencies:

- TCPIP
- UIP-UDP-PACKET
- UIP-NAMESERVER
- LIB/RANDOM
- SYS/PROCESS

### Verification status:

- no verification attempted
- probably quite hard to verify:
    - global variables
    - gotos
    - long functions with a lot of flags and constant

## SICSLOWPAN:

### Dependencies:

- NET/LINK-STATS
- UIPOPT
- TCPIP
- UIP
- UIP-DS6
- UIPBUF
- NET/NETSTACK
- NET/PACKETBUF
- NET/QUEUEBUF

### Verification status:

- absence of RTE started by Quentin Molle
- quite hard to verify:
   - globals variables
   - long functions with flags and constants
   - pointers retyping
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

### Dependencies:

- SYS/PROCESS
- LIB/LIST

### Verification status:

- no verification attempted
- some callback functions (requires \valid_function)
- talks with the scheduler

## UDP-SOCKET:

### Dependencies:

- SYS/PROCESS

### Verification status:

- no verification attempted
- process -> non natural loops

## UIP6:

### Dependencies

- UIP-ARCH
- UIPOPT
- UIP-ICMP6
- UIP-ND6
- UIP-DS6 (optionally + UIP-DS6-NBR)
- MULTICAST/UIP-MCAST6
- ROUTING/ROUTING
- SYS/LOG

### Verification status:

- no verification attempted
- does bad things with pointers and types
- a lot of global variables
- long functions
- gotos inside switches inside loops,
  with MACROS to deactivate parts of the code
- (no complex operations but bad ones)
- talk with timers
- uip_process is 1400 LOC long (have fun)

## UIPBUF:

### Dependencies:

- UIP

### Verification status:

- no verification attempted
- not too complex, just a single global to consider

## UIP-DEBUG:

- irrelevant for verification

## UIP-DS6:

### Dependencies:

- LIB/RANDOM
- UIP-ND6
- UIP-DS6
- UIP-DS6-NBR
- MULTICAST/UIP-MCAST6
- UIP-PACKETQUEUE

### Verification status:

- no verification attempted
- bad things with casts
- except for this the code is quite clean

## UIP-DS6-NBR:

### Dependencies:

- LIB/LIST
- NET/LINK-STATS
- NET/LINKADDR
- NET/PACKETBUF
- UIP-DS6
- UIP-ND6
- ROUTING/ROUTING

### Verification status:

- no verification attempted
- some global variables
- the code is quite clean but some part can be a bit tough to analyse

## UIP-DS6-ROUTE:

### Dependencies:

- LIB/LIST
- LIB/MEMB
- NBR-TABLE
- UIP-DS6
- UIP-DS6-ROUTE
- UIP

### Verification status:

- no verification attempted
- the dependencies to LIST, MEMB and NBR-TABLE could lead to complex
  contracts
- some functions are quite long

## UIP-ICMP6:

### Dependencies:

- UIP-DS6
- UIP-ICMP6
- ROUTING/ROUTING
- LIB/LIST

### Verification status:

- no verification attempted
- bad things with casts
- not so complex but relies on complex specifications

## UIPLIB:

### Dependencies:

- UIP
- IP64-ADDR

### Verification status:

- no verification attempted
- should be quite easy to verify for absence of RTE
- needs specification from IP64 however

## UIP-NAMESERVER:

### Dependencies:

- LIB/LIST
- LIB/MEMB

### Verification status:

- no verification attempted
- the code is not too complex but LIST/MEMB can lead to complex specs

## UIP-ND6:

### Dependencies:

- LIB/RANDOM
- UIP-ICMP6
- UIP-ND6
- UIP-DS6
- UIP-NAMESERVER

### Verification status:

- no verification attempted
- a lot of global variables
- long functions with gotos
- bad things with casts

## UIP-PACKETQUEUE:

### Dependencies:

- LIB/MEMB
- SYS/CTIMER

### Verification status:

- no verification attempted
- the code is quite simple
- some functions are transmitted as callbacks

## UIP-SR:

### Dependencies:

- ROUTING/ROUTING
- LIB/LIST
- LIB/MEMB

### Verification status:

- no verification attempted
- the code is not too complex but spec could be

## UIP-UDP-PACKET:

### Dependencies:

- MULTICAST/UIP/MCAST6

### Verification status:

- no verification attempted
- should not be too hard

## Macros or extern APIs libs :

- UIP-ARCH
- UIPOPT