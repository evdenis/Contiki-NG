# Core libraries

## AES-128:

### Dependencies:

- None

### Verification status:

- minimal-contracts for RTEs by Alexandre Peyrard
- finished ?
- functional correctness probably hard (would also require RPP)

## ASSERT:

### Dependencies:

- None

### Verification status:

- RTEs OK without annots
- (functional correctness is not relevant)

## CCM-STAR:

### Dependencies:

- AES-128

### Verification status:

- minimal-contracts for RTEs
- finished ?
- functional correctness probably hard (would also require RPP)

## CIRCULAR-LIST:

### Dependencies:

- None

### Verification status:

- no verification attempted
- LIST results could be partially used
- potentially requires a lot of work
    - RTEs probably requires functional correctness

## CRC16:

### Dependencies:

- None

### Verification status:

- minimal-contracts for RTEs
- functional correctness would probably require RPP plugin

## DBL-CIRC-LIST:

### Dependencies:

- None

### Verification status:

- no verification attempted
- LIST results could be partially used
- potentially requires a lot of work
    - RTEs probably requires functional correctness

## DBL-LIST:

### Dependencies:

- None

### Verification status:

- no verification attempted
- LIST results could be used
    - absence of RTEs requires functional correctness

## HEAPMEM:

### Dependencies:

- None

### Verification status:

- no verification attempted
- Absence of RTEs seems to require functional correctness
- functional correctness probably requires to improve WP
    - handling of allocated/freed/dangling/... required

## IFFT:

### Dependencies:

- None

### Verification status:

- minimal-contracts for RTEs

## LIST:

### Dependencies:

- None

### Verification status:

- functional verification performed by Allan Blanchard

## MEMB:

### Dependencies:

- None

### Verification status:

- functional verification partially performed by Frédéric Mangano
- for FULL functional correctness
    - handling of allocated/freed/dangling/... required

## QUEUE:

### Dependencies:

- LIST

### Verification status:

- no verification attempted
- direct application of LIST

## RANDOM:

### Dependencies:

- None

### Verification status:

- RTEs OK without annots

## RINGBUF:

### Dependencies:

- None

### Verification status:

- minimal-contracts for RTEs

## RINGBUFINDEX:

### Dependencies:

- None

### Verification status:

- minimal-contracts for RTEs

## SENSORS:

### Dependencies:

- None

### Verification status:

- no verification attemted
- requires support for unsized arrays

## STACK:

### Dependencies:

- LIST

### Verification status:

- no verification attempted
- direct application of LIST

## TRICKLE-TIMER:

### Dependencies:

- SYS/CC
- SYS/CTIMER
- RANDOM

### Verification status:

- no verification attempted
- dependent on sys/cc and sys/ctimer