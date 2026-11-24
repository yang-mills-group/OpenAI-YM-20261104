import YM.Integration.WilsonEmittedRootedFinance

/-! The stage already pays the weight converting a finite winding error at
the flat jet into an original held Wilson derivative on its parent patch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedWindingFinance
open Marker Wilson RG Lattice RG.Supply
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonEmittedDictionary WilsonEmittedStageFinance
variable {G:Gauge}

theorem anchor (tube:LinkTube G) (X:Patch) (K:KernelChoices) (O:Stage) (B:BudgetPoint)
    (k a:ℕ) {H Ω:ℝ} (ord:B.order=O.order) (power:B.power=O.power)
    (hg:0≤Real.log H) (square:B.B=Nat.ceil ((Real.log H)^2)) (within:a≤B.B)
    (funded:(program tube X K O k)^3*(1+Real.log H)^(orderBill X O k) ≤ Ω) :
    Anchor.focus a 0 B^B.order * groupPrice tube B.order ≤ Ω := by
  let C:=program tube X K O k
  let z:=1+Real.log H
  let E:=2*B.power*B.order
  have parts:=WilsonEmittedStageFinance.parts tube X K O k
  have one:1≤C:=parts.1
  have big:1≤z:=by dsimp [z];linarith
  have c0:0≤C:=zero_le_one.trans one
  have z0:0≤z:=zero_le_one.trans big
  have live:groupPrice tube B.order ≤ C:=by rw [ord];exact (le_abs_self _).trans parts.2.1
  have first:Anchor.focus a 0 B^B.order ≤ C*z^E:=(WilsonEmittedShortTariff.focus B hg square within).trans
    (mul_le_mul_of_nonneg_right (by rw [power,ord];exact parts.2.2.1) (pow_nonneg z0 _))
  have exp:E≤orderBill X O k:=by unfold E orderBill;rw [ord,power];omega
  calc
    _ ≤ (C*z^E)*C:=mul_le_mul first live (price_nonneg tube B.order) (mul_nonneg c0 (pow_nonneg z0 _))
    _ = C^2*z^E:=by ring
    _ ≤ C^3*z^(orderBill X O k):=mul_le_mul (pow_le_pow_right₀ one (by decide))
      (pow_le_pow_right₀ big exp) (pow_nonneg z0 _) (pow_nonneg c0 _)
    _ ≤ Ω:=funded

end YM.Integration.WilsonEmittedWindingFinance
