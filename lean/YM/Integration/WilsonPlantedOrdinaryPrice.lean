import YM.Integration.WilsonPlantedOrdinary

/-! The common source toll is restored once in each actual partition.
The housing and moving-test costs remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPlantedOrdinaryPrice
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Push.Corrected
open Source Labels Planned.GuardedAtom Extra.Histories WilsonCenteredCaptureRegularAtoms WilsonCenteredLampCapture
open WilsonCenteredFiledAtoms WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftRoster
open WilsonRootedKioskOccupiedSlip Comparison.RG02.Cumulants
open WilsonCapturedPrimarySoftMount (cost)
open scoped Classical BigOperators
variable {n : Side} {V : Type} [DecidableEq V] {R : Census V}

private theorem joint (w : V→ℝ) (s : R.Mode) (q : (parts R).Mode) (admitted : q∈shards R s)
    (hw : ∀v,0<w v) (p : BudgetPoint) (Z : Support n) (C:ℝ) :
    Poly.toll w s * tariff p Z w C q =
      Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*C^q.val.card := by
  have split : Poly.toll w s = ∏t∈q.val,Poly.toll w t.val := by
    rw [←show unionOf q=s from (mem_filter.mp admitted).2]
    exact prod_biUnion (parts_wise q)
  have book : (∏j,Poly.toll w (block q j))=Poly.toll w s := by
    rw [split]
    exact (Equiv.prod_comp (index q) (fun t:↥q.val=>Poly.toll w t.val.val)).trans
      (Finset.prod_coe_sort q.val (fun t=>Poly.toll w t.val))
  simp only [tariff,prod_mul_distrib,prod_inv_distrib,prod_const,card_univ,Fintype.card_fin,book]
  field_simp [(Poly.worth hw s).ne']

theorem partition (p : BudgetPoint) (Z : Support n) (rad : ℕ)
    (w : V→ℝ) (hw : ∀v,0<w v) (s : R.Mode) (q : (parts R).Mode) (admitted : q∈shards R s)
    {C D K:ℝ} (hc : 0≤C) (hd:0≤D) (c:C≤K) (d:D≤K) :
    Poly.toll w s * (cost p Z w C rad q+tariff p Z w D q) ≤
      (stage p rad (univ:Finset (Fin q.val.card))+1)*Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*K^q.val.card := by
  let S:=stage p rad (univ:Finset (Fin q.val.card))
  let E:=Real.exp ((p.supportExponent+2)*coverNumber p.B Z)
  have spos : 0≤S:=zero_le_one.trans (funded p rad _)
  have epos : 0≤E:=(Real.exp_pos _).le
  have a:=joint w s q admitted hw p Z C
  have b:=joint w s q admitted hw p Z D
  calc
    _ = S*(Poly.toll w s*tariff p Z w C q)+Poly.toll w s*tariff p Z w D q :=by unfold cost; dsimp only [S];ring
    _ = S*(E*C^q.val.card)+E*D^q.val.card:=by rw [a,b]
    _ ≤ S*(E*K^q.val.card)+E*K^q.val.card:=add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc c _) epos) spos)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd d _) epos)
    _ = _:=by dsimp only [S,E];ring

end YM.Integration.WilsonPlantedOrdinaryPrice
