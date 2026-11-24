import YM.Integration.WilsonThermometerFullSignedRent
import YM.Integration.WilsonPlantedOrdinaryHalo

/-! Quantitative charges for the three signed pieces of an ordinary capture
on its funded spatial halo. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFullFaceSignedHalo
open Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Source Labels Planned.GuardedAtom Extra.Histories
open WilsonCenteredMaskPieces WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftMount WilsonCenteredLampCapture
open WilsonCenteredMixedSetFiling WilsonCenteredFiledAtoms WilsonThermometerCenteredAlgebra
open scoped BigOperators Classical
variable {n : Side} {V : Type} [DecidableEq V] {R : Census V} {G : Gauge} {d : ℕ} {F : Frame G d}
local notation "J" => Stock.census (Fin 3)

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

def roof (α K : ℝ) : ℝ :=
  (Fintype.card (parts J).Mode:ℝ)*Real.exp ((α+2)*81)*K^3

private theorem roots (p : BudgetPoint) (w : Fin 3→ℝ) (hw : ∀v,0<w v) (s : (J).Mode)
    (y : Site n) (Z : Support n) (housed : Z⊆halo p.B {y}) {α C K : ℝ} (strength : p.supportExponent≤α)
    (cpos : 0≤C) (cap : C≤K) (one : 1≤K) :
    Poly.toll w s*WilsonCapturedPrimarySoftInventory.fare p Z w C s≤roof α K :=by
  unfold WilsonCapturedPrimarySoftInventory.fare
  rw [mul_sum]
  have each (q : (parts (J)).Mode) (ok : q∈shards (J) s) :
      Poly.toll w s*tariff p Z w C q ≤ Real.exp ((α+2)*81)*K^3 :=by
    rw [joint w s q ok hw p Z C]
    have sz: q.val.card≤3 := (WilsonCapturedPrimarySoftLoad.size ok).trans (by simpa using card_le_univ s.val)
    exact mul_le_mul (WilsonCenteredCaptureGeometry.cover p Z y housed strength)
      ((pow_le_pow_left₀ cpos cap _).trans (pow_le_pow_right₀ one sz)) (pow_nonneg cpos _) (Real.exp_nonneg _)
  have sum: (∑ q∈shards (J) s,Poly.toll w s*tariff p Z w C q) ≤ ((shards (J) s).card:ℝ)*(Real.exp ((α+2)*81)*K^3):=by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum each
  have cnt:((shards (J) s).card:ℝ)≤Fintype.card (parts J).Mode:=by exact_mod_cast card_le_univ (shards (J) s)
  exact sum.trans <| (mul_le_mul_of_nonneg_right cnt (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (zero_le_one.trans one) _))).trans_eq (mul_assoc ..).symm

theorem slips (p : BudgetPoint) (w : Fin 3→ℝ) (hw : ∀v,0<w v) (s : (J).Mode)
    (y : Site n) (Z : Support n) (housed : Z⊆halo p.B {y}) {α C D K v κ : ℝ} (strength : p.supportExponent≤α)
    (cpos : 0≤C) (dpos : 0≤D) (cap : C≤K) (raw : D≤K) (one : 1≤K) (hv : 0≤v) (div : 0<κ) :
    Poly.toll w s*(∑q∈shards (J) s,WilsonFullFaceSignedMasks.charge p Z w C D v κ q) ≤
      (hitWidth p*v/κ)*(2*roof α K) :=by
  have fact : (∑q∈shards (J) s,WilsonFullFaceSignedMasks.charge p Z w C D v κ q)=
      (hitWidth p*v/κ)*(WilsonCapturedPrimarySoftInventory.fare p Z w C s+WilsonCapturedPrimarySoftInventory.fare p Z w D s) :=by
    unfold WilsonCapturedPrimarySoftInventory.fare
    rw [←sum_add_distrib,mul_sum]
    exact sum_congr rfl (fun q _=>by unfold WilsonFullFaceSignedMasks.charge;ring)
  have left:=roots p w hw s y Z housed strength cpos cap one
  have right:=roots p w hw s y Z housed strength dpos raw one
  rw [fact,mul_left_comm,mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith only [left,right]) (div_nonneg (mul_nonneg (by unfold hitWidth;positivity) hv) div.le)

theorem hard (p : BudgetPoint) (w : Fin 3→ℝ) (hw : ∀v,0<w v) (s : (J).Mode)
    (y : Site n) (Z : Support n) (housed : Z⊆halo p.B {y}) {α E K v κ income : ℝ} (strength : p.supportExponent≤α)
    (cpos : 0≤E) (cap : E≤K) (one : 1≤K) (hv : 0≤v) (div : 0<κ) (room : hitWidth p*v≤1)
    (positive : 0 ≤ income) (small : income≤1) :
    Poly.toll w s*WilsonFullFaceSignedHard.fee p Z w s E income v κ ≤
      (Fintype.card ((J).Mode × (J).Mode):ℝ)*(2*roof α K*(3*Real.exp 3)*(income/κ)) :=by
  let B:=roof α K
  let H:=hitWidth p*v
  have h0 : 0≤H:=mul_nonneg (by unfold hitWidth;positivity) hv
  have b0 : 0≤B:=by dsimp [B,roof];exact mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans one) _)
  let cash(t:(J).Mode):=WilsonCapturedPrimarySoftInventory.fare p Z w E t
  have seen (z : (J).Mode × (J).Mode) (ok : z∈WilsonFullFaceSignedHard.occupied s) :
      Poly.toll w s*((1+H)*price (cash z.1) w z.2 income/κ) ≤ 2*B*(3*Real.exp 3)*(income/κ) :=by
    have both:=valid (mem_filter.mp ok).1
    have each : Poly.toll w s=(Poly.toll w z.1)*(Poly.toll w z.2) :=by
      unfold Poly.toll
      rw [←both.2,prod_union both.1]
    let T:ℝ:=z.2.val.card
    have t0 : 0≤T:=Nat.cast_nonneg _
    have t3 : T≤3:=by dsimp only [T];exact_mod_cast (show z.2.val.card≤3 by simpa using card_le_univ z.2.val)
    have ex : 0≤Real.exp (T*income)-1:=sub_nonneg.mpr (Real.one_le_exp (mul_nonneg t0 positive))
    have rare : Real.exp (T*income)-1 ≤ (3*Real.exp 3)*income :=
      (WilsonCenteredOccupiedHardSets.divided t0 positive small).trans
        ((mul_le_mul (mul_le_mul_of_nonneg_right t3 positive) (Real.exp_le_exp.mpr t3)
          (Real.exp_nonneg _) (mul_nonneg (by norm_num) positive)).trans_eq (by ring))
    have rows:=roots p w hw z.1 y Z housed strength cpos cap one
    have r0 : 0≤cash z.1:=by
      unfold cash WilsonCapturedPrimarySoftInventory.fare
      exact sum_nonneg fun t _=>mul_nonneg (Real.exp_nonneg _) <| prod_nonneg fun j _=>mul_nonneg
        (inv_nonneg.mpr (Poly.worth hw _).le) cpos
    have first : (1+H)*(Poly.toll w z.1*cash z.1)≤2*B :=
      mul_le_mul (by linarith only [room,show H=hitWidth p*v from rfl]) rows (mul_nonneg (Poly.worth hw _).le r0) (by norm_num)
    calc
      _ = (1+H)*(Poly.toll w z.1*cash z.1)*(Real.exp (T*income)-1)/κ :=by
        rw [each];unfold price;dsimp only [T]
        field_simp [(Poly.worth hw z.2).ne']
      _ ≤ (2*B*((3*Real.exp 3)*income))/κ :=
        div_le_div_of_nonneg_right (mul_le_mul first rare ex (mul_nonneg (by norm_num) b0)) div.le
      _ = _ :=by ring
  unfold WilsonFullFaceSignedHard.fee
  rw [mul_sum]
  have bound := sum_le_sum seen
  simp only [sum_const,nsmul_eq_mul] at bound
  refine bound.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact_mod_cast card_le_univ (WilsonFullFaceSignedHard.occupied s)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) b0) (by positivity)) (div_nonneg positive div.le)

end YM.Integration.WilsonFullFaceSignedHalo
