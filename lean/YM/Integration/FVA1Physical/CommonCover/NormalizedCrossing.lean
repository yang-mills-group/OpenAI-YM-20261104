import YM.Integration.FVA1Physical.CommonCover.OriginalClippedCrossing
import YM.Integration.WilsonReportNormalizedGallery

/-! Use the two physical single-source readings on the same unmodified
gallery. Once these and their regular terms are paid, the squared crossing
cost is linear in the raw four-coordinate error, even on a flagged field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Crossing
open Finset Lattice RG Wilson Marker QuadraticLocal Extra.Trajectories Exchange.RoseCut
open Push.AbsoluteSums.Animals
open scoped Classical BigOperators

theorem clipped_linear {ν W M a b A B : ℝ} (gas : 0 < ν) (cross : 0 ≤ W)
    (gross : 0 ≤ M) (ap : 0 ≤ a) (bp : 0 ≤ b) (ha : a/ν ≤ A) (hb : b/ν ≤ B) :
    (min M (invoice ν W M a b))^2 * ν ≤ M*(2*W*(M+(1+A)*(1+B))) := by
  let q := min M (invoice ν W M a b)
  have pos : 0 ≤ q := le_min gross (by unfold invoice; positivity)
  have reach : q*ν ≤ 2*W*(M+(1+A)*(1+B)) := by
    calc
      q*ν ≤ invoice ν W M a b * ν := mul_le_mul_of_nonneg_right (min_le_right ..) gas.le
      _ = 2*W*(M+(1+a/ν)*(1+b/ν)) := div_mul_cancel₀ _ gas.ne'
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul
        (add_le_add le_rfl ha) (add_le_add le_rfl hb) (by positivity)
        (add_nonneg zero_le_one ((div_nonneg ap gas.le).trans ha)))) (by positivity)
  calc
    q^2*ν = q*(q*ν) := by ring
    _ ≤ _ := mul_le_mul (min_le_left ..) reach (mul_nonneg pos gas.le) gross

variable {G : Gauge} {n : Side} {V T I : Type} [Fintype V] [DecidableEq V]
  {C : Census V} {o : V → Site n} {P : Rep G n} (A : Gallery T I o P C)

/-- The normalized hard singleton is exactly the difference between the
physical normalized singleton and the actual regular logarithm at that site. -/
theorem normalized_singleton_cost {w : V → ℝ} (wp : ∀ v,0 < w v) {e c κ : ℝ}
    (paid : A.Pays w e c κ) (en : 0 ≤ e) (t : T) (U : Config G n) (live : 0 < P.eval U)
    (v : V) (full reg : ℝ)
    (physical : ‖(w v : ℂ)*(((P.eval U : ℂ)⁻¹ • A.density t U).part (C.fire v))‖ ≤ full)
    (regular : ‖(w v : ℂ)*(A.E.log t U).part (C.fire v)‖ ≤ reg) :
    rawSingleton A t w v U/P.activities.gas P.p U ≤ full+reg := by
  let ν := P.activities.gas P.p U
  let X := (P.eval U : ℂ)⁻¹ • A.density t U
  let K := (ν : ℂ)⁻¹ • A.gas t U
  have gp : 0 < ν := pos_of_mul_pos_right live (Real.exp_nonneg _)
  have xu : X.part C.quiet = 1 := by
    rw [show X.part C.quiet = _ from Poly.part_smul .., A.same paid en wp,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr live.ne')]
  have ku : K.part C.quiet = 1 := by
    change ((ν : ℂ)⁻¹ • A.gas t U).part C.quiet = 1
    rw [Poly.part_smul,Gallery.gas,Hard.packet_of_quiet A.K t U
      (Hard.packet_summing _ paid.wages en wp t U), inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr gp.ne')]
  have same := WilsonReportNormalizedGallery.connected A wp en paid.wages t U live
  change connected X = A.E.log t U + connected K at same
  have coord := congrArg (fun Q : Poly C => Q.part (C.fire v)) same
  change (connected X).part (C.fire v) = (A.E.log t U + connected K).part (C.fire v) at coord
  rw [Poly.part_plus,Comparison.RG02.Cumulants.lamp v X xu,Comparison.RG02.Cumulants.lamp v K ku] at coord
  have resolved : (w v : ℂ)*K.part (C.fire v) =
      (w v : ℂ)*X.part (C.fire v) - (w v : ℂ)*(A.E.log t U).part (C.fire v) := by rw [coord]; ring
  have price := (norm_sub_le ((w v:ℂ)*X.part (C.fire v)) ((w v:ℂ)*(A.E.log t U).part (C.fire v))).trans
    (add_le_add physical regular)
  rw [← resolved] at price
  have divide : (w v : ℂ)*K.part (C.fire v) = ((w v : ℂ)*(A.gas t U).part (C.fire v)) / (ν:ℂ) := by
    change (w v : ℂ)*(((ν:ℂ)⁻¹ • A.gas t U).part (C.fire v)) = _
    rw [Poly.part_smul, div_eq_mul_inv]; ring
  rwa [divide,norm_div,Complex.norm_real,Real.norm_of_nonneg gp.le] at price

theorem original_linear_crossing (t : T) (a b : V) (s : C.Mode) (pair : s.val = {a,b})
    (w : V → ℝ) (wp : ∀ v,0 < w v) (e c κ : ℝ) (paid : A.Pays w e c κ)
    (en : 0 ≤ e) (small : κ ≤ 1) (m D : ℕ)
    (far : m*(2*width P.p D) < separation (o a) (o b)) (U : Config G n) (live : 0 < P.eval U)
    (out : U ∉ crowd P.p.threshold (neighbors (m*(2*width P.p D)) (o a)) m)
    (δ : ℂ) (M : ℝ) (cap : ‖((w a:ℂ)*(w b:ℂ))*δ‖ ≤ M)
    (full reg : V → ℝ)
    (physical : ∀ v ∈ ({a,b} : Finset V), ‖(w v:ℂ)*(((P.eval U:ℂ)⁻¹ • A.density t U).part (C.fire v))‖ ≤ full v)
    (regular : ∀ v ∈ ({a,b} : Finset V), ‖(w v:ℂ)*(A.E.log t U).part (C.fire v)‖ ≤ reg v) :
    let τ : ℂ := (w a:ℂ)*(w b:ℂ)
    let W := crossingWallet A t a b s w D m U
    ‖τ*δ‖ ≤ ‖τ*(δ-filedRow A t s U)‖ +
      Real.sqrt ((M*(2*W*(M+(1+(full a+reg a))*(1+(full b+reg b)))))/P.activities.gas P.p U) := by
  intro τ W
  have gp : 0 < P.activities.gas P.p U := pos_of_mul_pos_right live (Real.exp_nonneg _)
  have source v (h : v ∈ ({a,b} : Finset V)) := normalized_singleton_cost A wp paid en t U live v
    (full v) (reg v) (physical v h) (regular v h)
  have raw := relative_field A t a b s pair w wp e κ paid.wages en small m D far U live out δ M cap
  rw [original_invoice A t a b s w D m M U live] at raw
  have bill := clipped_linear gp (original_wallet_nonneg A t a b s w D m U) ((norm_nonneg _).trans cap)
    (norm_nonneg _) (norm_nonneg _) (source a (by simp)) (source b (by simp))
  apply (clip_error cap (norm_nonneg _) raw).trans (add_le_add le_rfl ?_)
  exact (le_abs_self _).trans ((Real.sqrt_sq_eq_abs _).symm.le.trans (Real.sqrt_le_sqrt ((le_div_iff₀ gp).2 bill)))

end YM.Integration.FVA1Physical.Crossing
