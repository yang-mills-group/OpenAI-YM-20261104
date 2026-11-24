import YM.Integration.WilsonPositionPrescribedFormalTest

/-! The actual formal MS root, evaluated as a finite polynomial, violates
the original finite physical normalization equations by only the next power.
The measurement is real-linear and uses exactly the stored joint test menu. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedFormalResidual
open Function PowerSeries Filter Set Finset Metric MeasureTheory Extraction Table Spec OPE Climb PhysMS Maxwell
open Trace.Pilot XSpace XSpace.Normalize FVA2 FVA2.Arrival MS MS.Land
open WilsonPositionPrescribedFormalTest
open scoped Topology BigOperators Classical
variable {G : Gauge} (V : Store G) (ν : ℝ)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (d q : ℕ)

private def filed (t : ℝ) : Prediction G d :=
  ∑ e ∈ range (q+1),t^e • Reg.State.author ν V T d e

private lemma watchFiled (W : Window G d) (t : ℝ) :
    watch W (filed V ν T d q t) =
      ∑ e∈range (q+1),(t:ℂ)^e * Reg.State.author ν V T d e W.n W.t W.p := by
  rw [filed,map_sum]
  apply sum_congr rfl
  intro e _
  rw [map_smul,Complex.real_smul,Complex.ofReal_pow]
  rfl

private lemma menuSolved (t : ℝ) : (V.measure d).D (filed V ν T d q t) =
    (V.measure d).D (reference G d) := by
  have solved (e : ℕ) : (V.measure d).D (Reg.State.author ν V T d e) =
      if e=0 then (V.measure d).D (reference G d) else 0 := (Reg.State.success ν V T).2.1 e
  simp only [filed,map_sum,map_smul,solved,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_range,
    Nat.zero_lt_succ,if_true,pow_zero,one_smul]

private lemma stamped (P : Prediction G d) : (V.survey d).stamps
    (fun i=>watch ((V.survey d).scope i) P) = guide G d ((V.measure d).D P) := by
  change guide G d ((V.survey d).tally _) = _
  rw [(V.survey d).equal]

private lemma base : (V.survey d).itinerary (V.survey d).opening =
    guide G d ((V.measure d).D (reference G d)) := by
  change (V.survey d).itinerary ((V.survey d).purse _,0) = _
  rw [(V.survey d).way]
  have h : recruit (Fray.box (0:MoveSpace G d)) (reference G d) = reference G d := by
    rw [Fray.box,map_zero,stand0]
    rfl
  rw [h]

private def trial (t : ℝ) := recruit (stand (turn V ν T d q t)) (raw ν T d q t)
private def bills (t : ℝ) (i : Fin (V.survey d).n) :=
  watch ((V.survey d).scope i) (trial V ν T d q t) - watch ((V.survey d).scope i) (filed V ν T d q t)

private theorem posted (t : ℝ) : (V.survey d).itinerary
    (WilsonPositionPrescribedTariff.target V ν T d q t,guide G d (turn V ν T d q t)) -
    (V.survey d).itinerary (V.survey d).opening = (V.survey d).stamps (bills V ν T d q t) := by
  rw [←menu,(V.survey d).way,base,←menuSolved V ν T d q t]
  have h : Fray.box (guide G d (turn V ν T d q t)) = stand (turn V ν T d q t) := by
    rw [Fray.box,LinearEquiv.symm_apply_apply]
  rw [h]
  change guide G d ((V.measure d).D (trial V ν T d q t)) - _ = _
  rw [←stamped,←stamped,←map_sub]
  rfl

theorem paid :
    ∃ C : ℝ,0≤C ∧ ∀t : ℝ,|t|≤1 →
      ‖(V.survey d).itinerary (WilsonPositionPrescribedTariff.target V ν T d q t,
          guide G d (turn V ν T d q t)) - (V.survey d).itinerary (V.survey d).opening‖ ≤ C*|t|^(q+1) := by
  classical
  let D := V.survey d
  have h (i : Fin D.n) : ∃ c : ℝ,0≤c ∧ ∀t : ℝ, |t|≤1 →
      ‖bills V ν T d q t i‖≤c*|t|^(q+1) := by
    obtain ⟨c,hc,hh⟩ := tested V ν T d q (D.scope i).t (D.scope i).p
    refine ⟨c,hc,fun t ht=>?_⟩
    rw [bills,watchFiled]
    exact hh t ht
  choose c cp rates using h
  let B := ∑ i,c i
  have pos : 0≤B := sum_nonneg (fun i _=>cp i)
  refine ⟨‖D.stamps‖*B,mul_nonneg (norm_nonneg _) pos,?_⟩
  intro t ht
  rw [posted,mul_assoc]
  refine (D.stamps.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg pos (pow_nonneg (abs_nonneg t) _))).2
  intro i
  exact (rates i t ht).trans (mul_le_mul_of_nonneg_right (single_le_sum
    (f:=c) (fun j _=>cp j) (mem_univ i)) (pow_nonneg (abs_nonneg t) _))

end YM.Integration.WilsonPositionPrescribedFormalResidual

