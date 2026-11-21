import PoissonDAG.Constructions.PORS.LiteralAssembly

open PoissonDAG PoissonDAG.PORS

/-- The outstanding premise concerns the literal circuit selected by the manifest. -/
theorem Submission.certificate
    (h : Literal.Refinement BucketRefined.p BucketRefined.p.rawEnvelope) :
    V2.ConstructionCertificate Literal.bucket 1492 :=
  Literal.bucket_conditional h
