import PoissonDAG.Constructions.PORS.LiteralAssembly

open PoissonDAG PoissonDAG.PORS

/-- The outstanding premise concerns the literal circuit selected by the manifest. -/
theorem Submission.certificate
    (h : Literal.Refinement SingleRefined.p SingleRefined.p.rawEnvelope) :
    V2.ConstructionCertificate Literal.single 1780 :=
  Literal.single_conditional h
