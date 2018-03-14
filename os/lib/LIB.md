# Core libraries

## AES-128:

- minimal-contracts for RTEs by Alexandre Peyrard
- finished ?
- functional correctness probably hard (would also require RPP)

## ASSERT:

- RTEs OK without annots
- (functional correctness is not relevant)

## CCM-STAR:

- minimal-contracts for RTEs
- finished ?
- functional correctness probably hard (would also require RPP)

## CIRCULAR-LIST:

- no verification attempted
- LIST results could be partially used
- potentially requires a lot of work
    - RTEs probably requires functional correctness

## CRC16:

- minimal-contracts for RTEs
- functional correctness would probably require RPP plugin

## DBL-CIRC-LIST:

- no verification attempted
- LIST results could be partially used
- potentially requires a lot of work
    - RTEs probably requires functional correctness

## DBL-LIST:

- no verification attempted
- LIST results could be used
    - absence of RTEs requires functional correctness

## HEAPMEM:

- no verification attempted
- Absence of RTEs seems to require functional correctness
- functional correctness probably requires to improve WP
    - handling of allocated/freed/dangling/... required

## IFFT:

- minimal-contracts for RTEs

## LIST:

- functional verification performed by Allan Blanchard

## MEMB:

- functional verification partially performed by Frédéric Mangano
- for FULL functional correctness
    - handling of allocated/freed/dangling/... required

## QUEUE:

- no verification attempted
- direct application of LIST

## RANDOM:

- RTEs OK without annots

## RINGBUF:

- minimal-contracts for RTEs

## RINGBUFINDEX:

- minimal-contracts for RTEs

## SENSORS:

- no verification attemted
- requires support for unsized arrays

## STACK:

- no verification attempted
- direct application of LIST

## TRICKLE-TIMER:

- no verification attempted
- dependent on sys/cc and sys/ctimer