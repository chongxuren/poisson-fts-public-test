import PoissonDAG.Constructions.PORS.LiteralAssembly

open PoissonDAG PoissonDAG.PORS

/-- The outstanding premise concerns the literal circuit selected by the manifest. -/
theorem Submission.certificate
    (h : Literal.Refinement ChainRefined.p (ChainRefined.p.simplexEnvelope ChainRefined.coefs)) :
    V2.ConstructionCertificate Literal.chainBuckets 1188 :=
  Literal.chain_conditional h
