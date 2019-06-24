# System modules

## AUTOSTART:

### Dependencies:

- PROCESS

### Verification status:

- no verification attempted
- requires support for unsized arrays
- requires contracts from PROCESS

## COMPOWER:

### Dependencies:

- ENERGEST
- NET/PACKETBUF // <-- Why ?

### Verification status:

- no verification attempted
- does not seem complex for RTE

## CTIMER:

### Dependencies:

- LIB/LIST

### Verification status:

- no verification attempted
- lists could make specification complex
- for unsupported non-natural loops
    - maybe with some new features in Conc2Seq

## ENERGEST:

### Dependencies:

- None

### Verification status:

- RTEs OK without annots

## ETIMER:

### Dependencies:

- PROCESS

### Verification status:

- no verification attempted
- for unsupported non-natural loops
    - maybe with some new features in Conc2Seq

## LOG:

### Dependencies:

- NET/IPV6/IP64-ADDR

### Verification status:

- no verification attempted
- does not seem complex for RTE
    - check how printing is done

## MUTEX + CRITICAL:

### Dependencies:

- None

### Verification status:

- no verification attempted
- does not seem complex for RTE  

## PROCESS:

### Dependencies:

- None

### Verification status:

- no verification attempted
- list manipulation but does not use the LIST module ...
- requires \valid_function
- recursive function
    - some work planned to remove recursion

## RTIMER:

### Dependencies:

- None (architecture)

### Verification status:

- no verification attempted
- requires \valid_function

## STACK-CHECK:

### Dependencies:

- LOG
- DEV/WATCHDOG

### Verification status:

- no verification attempted
- can be partially handled
- for unsupported non-natural loops
    - maybe with some new features in Conc2Seq
- `void*`

## STIMER:

### Dependencies:

- CLOCK

### Verification status:

- no verification attempted
- does not seem complex for RTE

## TIMER:

### Dependencies:

- CLOCK

### Verification status:

- no verification attempted
- does not seem complex for RTE

## Macros or extern APIs libs :

- PT
- PT-SEM
- LC
- LC-SWITCH
- LC-ADDRLABELS
- SUBPROCESS
- MEMORY-BARRIER
- PLATFORM
- INT-MASTER
- LOG-CONF
- CC-GCC
- CC
- CLOCK