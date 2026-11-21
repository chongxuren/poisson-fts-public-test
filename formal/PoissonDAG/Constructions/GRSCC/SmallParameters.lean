import PoissonDAG.Constructions.GRSCC.Kernel

/-! A small upper envelope for the local supplier probabilities.

The twenty rounded bounds below are certificate targets, not assumptions.
The one-history value follows from the constant-sum antichain theorem.
-/
namespace PoissonDAG.GRSCC.Small

def caps : List (List Nat) :=
  [[], [], [18262, 35826], [54856, 113911, 131665],
    [90305, 183260, 237005, 238152],
    [121721, 236736, 313172, 346531, 333683],
    [149671, 279213, 368050, 419215, 436118, 414374]]

def localUpper (m v : Nat) : Rat :=
  if v = 0 ∨ m < v then 0
  else if m = 1 then 1 / 15597
  else if m ≤ 6 then ((caps[m]?.getD [])[v-1]?.getD 0 : Rat) / 1000000
  else 1

def upperKernel (q current next : Nat) : Rat :=
  ((List.range current).map (fun v0 =>
    let v := v0 + 1
    if v ≤ next then
      binomialMass current v ((1 : Rat) / 32) * localUpper current v *
        binomialMass (q - current) (next - v) ((1 : Rat) / 32)
    else 0)).sum

def upperStep (q : Nat) (state : List Rat) : List Rat :=
  (List.range q).map (fun k => ((List.range q).map (fun j =>
    (state[j]?.getD 0) * upperKernel q (j + 1) (k + 1))).sum)

def upperChild (q : Nat) : Rat :=
  ((upperStep q)^[7] (initialState q)).sum

def boundedChild (q : Nat) : Rat := min (upperChild q) 1

end PoissonDAG.GRSCC.Small
