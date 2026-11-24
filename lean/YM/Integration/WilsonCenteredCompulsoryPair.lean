import YM.Integration.WilsonCenteredCompensatedPairRate
import YM.Next.MULTISOURCE.First

/-! The common measured hard gas contributes its quiet and the two proper
marked faces to a signed pair replacement. This computation uses the full
original polynomial and never divides by the hard gas. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCompulsoryPair
open Marker Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}

private theorem unit_product (a b c : V) (M : R.Mode)
    (apart : a ≠ b) (pair : M.val = {a,b}) (A B : Poly R)
    (ha : A.part R.quiet = 1) (hb : B.part R.quiet = 1) :
    (A*B).part M - (A*B).part (R.fire c) =
      (A.part M - A.part (R.fire c)) + (B.part M - B.part (R.fire c))
        + A.part (R.fire a) * B.part (R.fire b)
        + B.part (R.fire a) * A.part (R.fire b) := by
  have hprod : (A*B).part R.quiet = 1 := by rw [Poly.quiet_mul, ha, hb, one_mul]
  have h := congrArg (fun Z : Poly R => Z.part M) (connected_mul ha hb)
  change (connected (A*B)).part M = (connected A).part M + (connected B).part M at h
  rw [twins a b M _ hprod apart pair, twins a b M _ ha apart pair, twins a b M _ hb apart pair,
    Multi.first_mul A B a, Multi.first_mul A B b, ha, hb] at h
  rw [Multi.first_mul A B c,ha,hb]
  linear_combination h

/-- The three actual gas faces, with every deeper compulsory partner retained. -/
theorem original (a b c : V) (M : R.Mode) (apart : a ≠ b) (pair : M.val = {a,b})
    (A B G : Poly R) (ha : A.part R.quiet = 1) (hb : B.part R.quiet = 1) :
    ((A*G).part M - (A*G).part (R.fire c)) - ((B*G).part M - (B*G).part (R.fire c)) =
      G.part R.quiet * ((A.part M - A.part (R.fire c)) - (B.part M - B.part (R.fire c)))
        + (A.part (R.fire a) - B.part (R.fire a))*G.part (R.fire b)
        + G.part (R.fire a)*(A.part (R.fire b) - B.part (R.fire b)) := by
  let d := G.part R.quiet - 1
  let J := G - d • (1 : Poly R)
  have jq : J.part R.quiet = 1 := by
    change G.part R.quiet - d * (1 : Poly R).part R.quiet = 1
    rw [Poly.one_part, if_pos rfl, mul_one]
    dsimp [d]
    ring
  have jmark (v : V) : J.part (R.fire v) = G.part (R.fire v) := by
    change G.part (R.fire v) - d * (1 : Poly R).part (R.fire v) = _
    rw [Poly.one_part, if_neg (R.fire_hot v), mul_zero, sub_zero]
  have changeGas (P : Poly R) : P*G = P*J + d • P := by
    have eq : J + d • (1 : Poly R) = G := sub_add_cancel _ _
    calc
      _ = P*(J+d•(1 : Poly R)) := congrArg (fun x : Poly R => P*x) eq.symm
      _ = _ := by rw [mul_add,mul_smul_comm,mul_one]
  have hA := unit_product a b c M apart pair A J ha jq
  have hB := unit_product a b c M apart pair B J hb jq
  rw [jmark a,jmark b] at hA hB
  rw [changeGas A,changeGas B]
  simp only [Poly.part_plus,Poly.part_smul]
  dsimp [d]
  linear_combination hA - hB

end YM.Integration.WilsonCenteredCompulsoryPair
