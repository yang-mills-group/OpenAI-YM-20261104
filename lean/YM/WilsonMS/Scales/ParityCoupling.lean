import YM.WilsonMS.Scales.ClockH
/-!
# Real series and tested coupling re-expression

We only compare reannouncing in a *real formal field basis*. The matrix
charts below the continuum prescription are always real-H.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
variable {P Q : ChartK G d} {F A : Cn}

structure Aware (U : Cn) : Prop where
  root : Rooted U
  paid : coeff 1 U = 1
  clean : Clean U

lemma Aware.counter (h : Aware F) : Aware (Counter F) := by
  let Q := F
  have he : coeff 1 Q ≠ 0 := by
    rw [show Q = F from rfl, h.paid]
    exact one_ne_zero
  refine ⟨Ice.born _, ?_, ?_⟩
  · have hp := tangential Q h.root h.paid (Counter Q)
    rw [counter_r h.root he, PowerSeries.coeff_one_X] at hp
    exact hp.symm
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let B := Counter Q
    have hh : PowerSeries.map (starRingEnd ℂ) Q = Q :=
      PowerSeries.ext fun i => (PowerSeries.coeff_map ..).trans (h.clean i)
    have hv : Rooted (PowerSeries.map (starRingEnd ℂ) B) := by
      unfold Rooted
      rw [PowerSeries.coeff_map, Ice.born, map_zero]
    have ht : Q.subst (PowerSeries.map (starRingEnd ℂ) B) = Q.subst B := by
      nth_rw 1 [← hh]
      rw [←
        FPS.substitute_ringHom (starRingEnd ℂ) Q
          (show constantCoeff B = 0 from
            (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm.trans (Ice.born _)),
        show Q.subst B = X from counter_l h.root he, PowerSeries.map_X]
    exact
      (PowerSeries.coeff_map ..).symm.trans
        (congr_arg (coeff n) (Ice.separate h.root he hv (Ice.born _) ht))

lemma Aware.extend {P' Q' : Cn} (hp : Aware P') (hQ : Aware Q') : Aware (P'.subst Q') := by
  refine ⟨(root_sub _ _ hQ.root).trans hp.root, (tangential _ hQ.root hQ.paid _).trans hp.paid, ?_⟩
  intro n
  rw [usePool hQ.root]
  simp_rw [star_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [star_mul', hQ.clean.powers _ _, hp.clean]

lemma Aware.identity : Aware X := by
  constructor
  · rw [Rooted]
    simp
  · simp
  intro i
  by_cases h : i = 1 <;> simp [h, PowerSeries.coeff_X]
section stamp
variable {V : Store G} (W : Rose.Pick V) {P' Q' : ChartK G 6} {X' : Reports G 6}

lemma obs_equ (h : Equad P' Q') : observed W (P' 3) = observed W (Q' 3) := by
  have he : observe W (P' 3) = observe W (Q' 3) := by
    apply PowerSeries.ext
    intro n
    rw [observe, observe, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    exact
      Test.apply_eq _
        (fun x hx => by
          dsimp only [plays]
          rw [h 3 hx])
  unfold FrameConj.observed
  rw [he]

lemma ob_unit (hp : Rooted A) (h : FundsK (P' 3) X') :
    observe W ((Sub A P') 3) = (observe W (P' 3)).subst A := by
  refine PowerSeries.ext fun i => ?_
  have he (p : Points 3) : plays ((Sub A P') 3) p = (plays (P' 3) p).subst A := transept hp (P' 3 p)
  simp_rw [observe, PowerSeries.coeff_mk, usePool hp]
  let t := Rose.test W
  unfold Test.applyTo
  simp_rw [PowerSeries.coeff_mk, he, usePool hp, Finset.mul_sum,
    show
      ∀ p j,
        Rose.test W p * (cut A j i * coeff j (plays (P' 3) p)) =
          cut A j i * (Rose.test W p * coeff j (plays (P' 3) p))
      from fun _ _ => mul_left_comm ..]
  rw [integral_finsetSum _ (fun j _ => (t.smearing (FrameConj.tender h j)).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

lemma ob_sub (hp : Rooted A) (h : FundsK (P' 3) X') :
    observed W ((Sub A P') 3) = (observed W (P' 3)).subst A := by
  unfold FrameConj.observed
  rw [ob_unit W hp h, PowerSeries.subst_smul (Worried hp), PowerSeries.subst_sub (Worried hp),
    show
      (PowerSeries.C (coeff 0 (observe W (P' 3)))).subst A =
        PowerSeries.C (coeff 0 (observe W (P' 3)))
      from PowerSeries.subst_C _]
  dsimp only
  rw [root_sub _ _ hp]
end stamp
end YM.WilsonMS.GFlow
