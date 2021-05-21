# HIT Me with Your Best STLC

This is my Bachelor's thesis. The pdf of the thesis can be found in the `paper` directory

In `src/isomorphism` is the fully proven isomorphism between normal forms and
terms modulo βη-equivalence, along with the source code from "Hereditary
Substitution" adapted to work without K. The main isomorphism result is in
`src/isomorphism/iso.agda`.

`src/experiments` contains the two earlier attempts at working with quotiented
terms described in section 4 of the paper.

`src/translation` contains direct translations of some of the lemmas from
"Hereditary Substitution" to work with path equality, as described in section
6.2. 
