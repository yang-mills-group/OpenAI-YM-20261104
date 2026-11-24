import YM.Integration.WilsonCapturedPrimaryAngles
import YM.Next.FLUCTUATIONS.Charts

/-! The clipped axial test fields lie in the physical empty-flag chamber
at a period independent argument size. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryAperture
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Planned.AtomRegular Next.Foundations
open WilsonCapturedPrimaryAngles WilsonCapturedPrimaryRough
open Finset
open scoped Classical ContDiff Topology
attribute [local instance] Gauge.frobInner

private theorem tube (G : Gauge) : ∃ α : ℝ, 0<α ∧ α≤1 ∧ ∀ (n : Side) (P : BudgetPoint)
    (v : Directions G n), ‖v‖ ≤ α*P.threshold → flags P.threshold (increment 1 v)=∅ := by
  obtain ⟨C,δ,hC,hδ,bill⟩ := Next.Fluctuations.chord_chart_cost G
  let a := min 1 (min δ (4*C)⁻¹)
  have pos : 0<a := lt_min zero_lt_one (lt_min hδ (inv_pos.mpr (by positivity)))
  have one : a≤1 := min_le_left ..
  have ha : a≤δ := (min_le_right ..).trans (min_le_left ..)
  have hc : a≤(4*C)⁻¹ := (min_le_right ..).trans (min_le_right ..)
  refine ⟨a,pos,one,?_⟩
  intro n P v hv
  let U : Config G n := increment 1 v
  have bounded (e : Link n) : ‖v e‖ ≤ a*P.threshold := (norm_le_pi_norm v e).trans hv
  have each (e : Link n) : G.chord (U e) ≤ C*(a*P.threshold) := by
    have small := (bounded e).trans ((mul_le_of_le_one_right pos.le P.threshold_le).trans ha)
    simpa only [U,increment,Pi.one_apply,mul_one] using
      ((bill (v e) small).trans (mul_le_mul_of_nonneg_left (bounded e) hC.le))
  have travelPrice (word : Walk) (x : Site n) :
      G.chord (travel U x word) ≤ word.length*(C*(a*P.threshold)) := by
    induction word generalizing x with
    | nil => simp [travel]
    | cons d w ih =>
      have letter : G.chord (d.read U x) ≤ C*(a*P.threshold) := by
        by_cases hn : d.neg
        · rw [Lattice.Step.read,if_pos hn,G.chord_inv]; exact each _
        · rw [Lattice.Step.read,if_neg hn]; exact each _
      simpa only [travel,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm]
        using (G.chord_triangle ..).trans (add_le_add letter (ih (x+d.vec)))
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨z,_,bad⟩ := (flags_spec ..).mp hx
  have pay : 4*C*a≤1 := (mul_le_mul_of_nonneg_left hc (show 0≤4*C by positivity)).trans_eq
    (mul_inv_cancel₀ (by positivity))
  have healthy := travelPrice (square z.2.val.1 z.2.val.2) z.1
  change G.chord (faceValue U z) ≤ 4*(C*(a*P.threshold)) at healthy
  exact (not_lt_of_ge (healthy.trans ((show 4*(C*(a*P.threshold))=4*C*a*P.threshold by ring).le.trans
    (mul_le_of_le_one_left P.threshold_pos.le pay)))) bad

def aperture (G : Gauge) := (tube G).choose

theorem positive (G : Gauge) : 0<aperture G := (tube G).choose_spec.1

theorem atMostOne (G : Gauge) : aperture G ≤ 1 := (tube G).choose_spec.2.1

variable {G : Gauge} {n : Side} {d : ℕ}

theorem shifted (P : BudgetPoint) (v : Directions G n) (small : ‖v‖ ≤ aperture G * P.threshold) :
    flags P.threshold (increment 1 v) = ∅ := (tube G).choose_spec.2.2 n P v small

theorem weights (P : BudgetPoint) (o : Site n) (r : ℕ)
    (paid : P.threshold*(1+(r:ℝ))^2≤1) : ∀ e∈active o r, weight (quadratic P) o e≤1 := by
  intro e he
  have dist : separation e.1 o ≤ r := (mem_filter.mp he).2
  change P.threshold*(1+(separation e.1 o:ℝ))^2 ≤ 1
  have dd : (1:ℝ)+(separation e.1 o:ℝ)≤1+(r:ℝ) := by exact_mod_cast Nat.add_le_add_left dist 1
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) dd 2)
    P.threshold_pos.le).trans paid

theorem chart (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d)
    {t : ℝ} (one : |t|≤1) (paid : P.threshold*(1+(r:ℝ))^2≤1)
    (small : |t| * wallet A p r ≤ aperture G*P.threshold) :
    let v := limitAmp (quadratic P) o (active o r) (angular A P o r p t)
    ‖v‖ ≤ aperture G*P.threshold ∧ (∀ e∈active o r, ‖v e‖≤1) ∧
      flags P.threshold (WilsonCapturedPrimaryRays.field A P o r p t)=∅ := by
  intro v
  have h₀ := (size A P o r p one).trans small
  have hv : ‖v‖ ≤ aperture G*P.threshold := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (positive G).le P.threshold_pos.le)).2
    intro e
    by_cases he : e∈active o r
    · rw [show v e=weight (quadratic P) o e • angular A P o r p t e by simp [v,limitAmp,he],
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (weight_pos ..).le]
      exact (mul_le_of_le_one_left (norm_nonneg _) (weights P o r paid e he)).trans
        ((norm_le_pi_norm _ e).trans h₀)
    · simp [v,limitAmp,he]
      exact mul_nonneg (positive G).le P.threshold_pos.le
  have h₁ : aperture G*P.threshold ≤ 1 :=
    (mul_le_of_le_one_right (positive G).le P.threshold_le).trans (tube G).choose_spec.2.1
  exact ⟨hv,fun e _ => (norm_le_pi_norm v e).trans (hv.trans h₁),by
    rw [physical]; exact shifted P v hv⟩

end YM.Integration.WilsonCapturedPrimaryAperture
