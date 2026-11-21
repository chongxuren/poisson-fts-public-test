import PoissonDAG.Constructions.GRSCC.SmallParameters

/-! Two prior words use three degree counters (target, first history, second
history). Encode the triple of degrees in base 49 and each coefficient in
base 2^64. Six depth coordinates have degree at most 48 in each variable and
at most 9^18 assignments in total. Neither kind of digit can carry.
This arithmetic derives the two local counts directly from the supply rule;
identifying coefficient extraction with the protected finite experiment is
a separate theorem. -/
namespace PoissonDAG.GRSCC.TwoHistory

private def digitBits := 64
private def stride := 49
private def targetShift := digitBits * stride^2
private def targetDigits : Nat → Nat
  | 0 => 1
  | n+1 => (targetDigits n <<< targetShift) + 1

/-- For given history depths i,j the target may be any depth ≤ limit i j. -/
private def plane (limit : Nat → Nat → Nat) : Nat :=
  ((List.range 9).map (fun i => ((List.range 9).map (fun j =>
    targetDigits (limit i j) <<< (digitBits * (i + stride*j)))).sum)).sum

private def coeff (p : Nat) :=
  (p >>> (digitBits * (16 + stride*16 + stride^2*16))) % (2^digitBits)

def twoSame : Nat := coeff ((plane max)^6)

def oneSame : Nat :=
  let both := plane max
  let automatic := plane (fun _ _ => 8)
  let first := plane (fun i _ => i)
  ((List.range 5).map (fun d =>
    2^(4-d) * coeff (both^d * automatic * first^(5-d)))).sum

theorem no_carry : 6*8 < stride ∧ 9^18 < (2^digitBits : Nat) := by decide +kernel

set_option maxHeartbeats 0 in
theorem same_count : twoSame = 135928911021 := by decide +kernel

set_option maxHeartbeats 0 in
theorem mixed_count : oneSame = 2147987272652 := by decide +kernel

theorem local_caps :
    twoSame * 1000000 ≤ 35826 * 15597^3 ∧
    oneSame * 1000000 ≤ 18262 * 15597^3 * 31 := by
  rw [same_count, mixed_count]
  decide +kernel

end PoissonDAG.GRSCC.TwoHistory
