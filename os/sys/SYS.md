# System modules

## AUTOSTART:

- no verification attempted
- requires support for unsized arrays  

## COMPOWER:

- no verification attempted
- does not seem complex for RTE

## CTIMER:

- no verification attempted
- for unsupported non-natural loops
    - maybe with some new features in Conc2Seq

## ENERGEST:

- RTEs OK without annots

## ETIMER:

- no verification attempted
- for unsupported non-natural loops
    - maybe with some new features in Conc2Seq

## LOG:

- no verification attempted
- does not seem complex for RTE
    - check how printing is done

## MUTEX + CRITICAL:

- no verification attempted
- does not seem complex for RTE  

## PROCESS:

- no verification attempted
- list manipulation but does not use the LIST module ...
- requires \valid_function
- recursive function
    - some work planned to remove recursion

## RTIMER:

- no verification attempted
- requires \valid_function

## STACK-CHECK:

- no verification attempted
- can be partially handled
- for unsupported non-natural loops
    - maybe with some new features in Conc2Seq

## STIMER:

- no verification attempted
- does not seem complex for RTE
- dependent on clock

## TIMER:

- should be trivial to validate
- (still dependent on clock)


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