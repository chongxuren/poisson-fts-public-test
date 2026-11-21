# 2,020-byte FORS construction

There are 7 trees of height 17. Each signature transmits one committed leaf's private source and 17 sibling labels per tree. The maximum encoded size is 16 × 7 × (17+1) plus 4 counter bytes. The encoder uses 19 virtual zero bits and a 26-bit counter. Expected signing takes at most 3,801,087 hashes. A successful verification takes at most 134 hashes. The proof bounds the raw target covering probability by 2⁻¹²⁸ under one shared Poisson(1) history count.

The final Lean theorem proves the complete V2 construction goal for this exact circuit.
