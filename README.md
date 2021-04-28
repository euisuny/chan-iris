# chan-iris
Iris case study. A modification of ChanLang, a message passing calculus instantiated with iris.
There is a logically atomic heap specified which can store channels.
(WIP)

(See notes p.19-20)
## Specification
Chanlang atomic
unary heap lang
logically atomic heap

canonically..
message-passing

First step: Physically atomic
Logical atomicity
Linearizability: appear to happen atomically

buffer operations are logically atomic buffer => L.A. ref
channel : send/add channel

## References
* Iris from the Ground Up
* Iris 1.0 : logical atomicity
* Prophecy Variables https://plv.mpi-sws.org/prophecies/ (In particular, the POPL publication)
