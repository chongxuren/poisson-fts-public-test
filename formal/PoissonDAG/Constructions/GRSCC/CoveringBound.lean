import PoissonDAG.Constructions.GRSCC.Circuit
import PoissonDAG.Constructions.GRSCC.GraphSuppliers
import PoissonDAG.Constructions.GRSCC.GraphBridge

/-! The unconditional graph-to-kernel bound for the actual literal scheme. -/
namespace PoissonDAG.GRSCC

theorem coefficient_upper_of_refinement (encoder : Circuit) (href : CircuitRefines encoder)
    (q : Nat) :
    (schemeOfCircuit encoder).coverCoefficient q ≤ acceptanceRatio * bucketThinned q :=
  coefficient_upper_of_suppliers encoder href q (covered_accepted_route_supplied encoder href)

theorem scheme_coefficient_upper (q : Nat) :
    scheme.coverCoefficient q ≤ acceptanceRatio * bucketThinned q :=
  coefficient_upper_of_refinement literalCircuit literalCircuit_refines q

end PoissonDAG.GRSCC
