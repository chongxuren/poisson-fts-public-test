import PoissonDAG.Constructions.FORS.Authentication
import PoissonDAG.Constructions.FORS.Signing
import PoissonDAG.Constructions.FORS.Verification
import PoissonDAG.Constructions.FORS.LiteralPoisson
import PoissonDAG.Constructions.FORS.WellFormed

/-! Public challenge submissions for homogeneous FORS and its counter variant.
Each endpoint concerns the exact graph and Boolean encoder in Literal.lean. -/
namespace PoissonDAG.FORS

open Config

private theorem assemble (p : Config) (n : Nat) (ht : 2 ≤ p.trees) (hr : 0 < p.rawBits)
    (hf : p.scheme.failure ≤ (1:Rat)/2^128) (hs : p.scheme.signCost ≤ 2^24)
    (hv : p.scheme.digestCalls + p.trees*(p.height+1) + (p.trees-1) ≤ 441)
    (hcover : PoissonLE p.scheme.coverCoefficient ((1:Rat)/2^128))
    (hsize : (p.counterBits+7)/8 + 16*(p.trees*(p.height+1)) ≤ n) :
    V2.ConstructionCertificate p.scheme n := by
  have wf := p.wellFormed (by omega) hr
  have ha := wf.2.2.2.2.2
  exact ⟨⟨⟨wf,p.correct ht,hf,hs,p.verification_budget ha hv,hcover⟩,
    fun raw _ => p.authenticated raw ht⟩,p.size_upper.trans hsize⟩

theorem fors2432 : V2.ConstructionCertificate (scheme ⟨18,8,0,0⟩) 2432 := by
  apply assemble _ _ (by decide) (by decide)
  · rw [ordinary_sign_and_failure.2]; positivity
  · exact ordinary_sign_and_failure.1.trans (by decide)
  · decide +kernel
  · exact ordinary_literal_poisson
  · decide

theorem forsCounter2132 : V2.ConstructionCertificate (scheme ⟨18,7,18,25⟩) 2132 :=
  assemble _ _ (by decide) (by decide) equal_width_sign_and_failure.2
    (equal_width_sign_and_failure.1.trans (by decide)) (by decide +kernel)
    equal_width_literal_poisson (by decide)

theorem forsCounter2020 : V2.ConstructionCertificate (scheme ⟨17,7,19,26⟩) 2020 :=
  assemble _ _ (by decide) (by decide) variable_width_sign_and_failure.2
    (variable_width_sign_and_failure.1.trans (by decide)) (by decide +kernel)
    variable_width_literal_poisson (by decide)

#print axioms fors2432
#print axioms forsCounter2132
#print axioms forsCounter2020

end PoissonDAG.FORS

/-- Submitted proof for the organizer circuit named in program.json. -/
theorem Submission.certificate : PoissonDAG.V2.ConstructionCertificate
    (PoissonDAG.FORS.Config.scheme ⟨17, 7, 19, 26⟩) 2020 := PoissonDAG.FORS.forsCounter2020
