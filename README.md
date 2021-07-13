# chan-iris
Iris case study (WIP). 
An implementation of ChanLang, a message-passing calculus with non-blocking send,
receive, and fork operations.

## Specification
- [lang.v] : language definition, with usual small-step semantics of a
  message-passing calculus
- [network_ra.v] : the _physical state_ of the language, which has a similar
  structure to heaps in heaplang, except that here we keep track of the
  threadpool of channels.
- [class_instances.v] : contains physically atomic operations using the `Atomic`
  primitive.
- [primitive_laws.v] : primitive laws about the physically atomic operations.
    (Figure 11 from Iris 1.0 paper)
- [localchan.v] : logically atomic triples about chanlang. 
   ("Local channel assertions" from Iris 1.0 paper)
- [mutref.v] : mutable references implemented using channel primitives

## TODO
- mutable references on top of channels
- channels on top of mutable references

## References
* Iris from the Ground Up
* Iris 1.0 : logical atomicity
* Prophecy Variables https://plv.mpi-sws.org/prophecies/ (In particular, the POPL publication)
