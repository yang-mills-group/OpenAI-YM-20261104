import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedPaperOrdinary
import YM.Integration.WilsonGraphCartesianJetBound
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section
namespace YM.Integration.GradedFar.AppointedCartesianWords

open Set Filter
open YM.Integration.GradedFar.Tariff.Sunshine
open scoped Classical BigOperators ContDiff Topology

def trace {n : ℕ} : (k : ℕ) → (Fin k → Fin n × Axis) → TraceOrder n
  | 0, _ => []
  | k + 1, w => w (Fin.last k) :: trace k (Fin.init w)

set_option maxHeartbeats 1200000 in
set_option synthInstance.maxHeartbeats 120000 in
theorem onWord {n : ℕ} {X : Set (Points n)} (hX : IsOpen X)
    {f : Points n → ℂ} (hf : ContDiffOn ℝ ∞ f X) {x : Points n} (hx : x ∈ X)
    (k : ℕ) (w : Fin k → Fin n × Axis) :
    δ (trace k w) f x =
      iteratedFDeriv ℝ k f x (fun i => WilsonGraphCartesianJetBound.axis (w i)) := by
  induction k generalizing f with
  | zero => simp [trace, δ]
  | succ k ih =>
    let a := w (Fin.last k)
    let v : Fin k → Points n := fun i => Points.direction (Fin.init w i).1 (Fin.init w i).2
    letI : IsBoundedSMul ℝ E4 :=
      PiLp.instIsBoundedSMul (p := 2) (𝕜 := ℝ) (β := fun _ : Axis => ℝ)
    letI : IsBoundedSMul ℝ (Points n) :=
      PiLp.instIsBoundedSMul (p := 2) (𝕜 := ℝ) (β := fun _ : Fin n => E4)
    letI : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
    have hUnique : UniqueDiffOn ℝ X := hX.uniqueDiffOn
    have deriv : ContDiffOn ℝ ∞ (fderiv ℝ f) X := ((contDiffOn_infty_iff_fderiv_of_isOpen hX).1 hf).2
    have atVector := iteratedFDerivWithin_clm_apply_const_apply (𝕜 := ℝ)
      (E := Points n) (F := Points n) (G := ℂ) (s := X) (c := fderiv ℝ f) (n := ∞) hUnique deriv
      (i := k) (WithTop.coe_le_coe.mpr (show (k : ℕ∞) ≤ ⊤ from le_top)) hx (u := Points.direction a.1 a.2) (m := v)
    rw [iteratedFDerivWithin_of_isOpen (f := fun y => (fderiv ℝ f y) (Points.direction a.1 a.2)) k hX hx,
      iteratedFDerivWithin_of_isOpen (f := fderiv ℝ f) k hX hx] at atVector
    change δ (trace k (Fin.init w)) (Points.gradient a.1 a.2 f) x = _
    rw [ih (hf := smooth_grad hX hf a) (w := Fin.init w), iteratedFDeriv_succ_apply_right]
    exact atVector

theorem bound {n : ℕ} {X : Set (Points n)} (hX : IsOpen X)
    {f g : Points n → ℂ} (hf : ContDiffOn ℝ ∞ f X) (hg : ContDiffOn ℝ ∞ g X)
    {x : Points n} (hx : x ∈ X) (k : ℕ) (C : (Fin k → Fin n × Axis) → ℝ)
    (positive : ∀ w, 0 ≤ C w) {err : ℝ} (herr : 0 ≤ err)
    (paid : ∀ w, ‖δ (trace k w) f x - δ (trace k w) g x‖ ≤ C w * err) :
    ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x‖ ≤ (∑ w, C w) * err := by
  apply WilsonGraphCartesianJetBound.bound _ C positive herr
  intro w
  change ‖iteratedFDeriv ℝ k f x (fun i => WilsonGraphCartesianJetBound.axis (w i)) -
    iteratedFDeriv ℝ k g x (fun i => WilsonGraphCartesianJetBound.axis (w i))‖ ≤ _
  simpa only [onWord hX hf hx k w, onWord hX hg hx k w] using paid w

theorem uniform {n : ℕ} {α : Type*} {I : α → Type*} (F : Filter α)
    {X : Set (Points n)} (hX : IsOpen X)
    (f g : (s : α) → I s → Points n → ℂ) (point : (s : α) → I s → Points n)
    (inside : ∀ s u, point s u ∈ X) (smoothF : ∀ s u, ContDiffOn ℝ ∞ (f s u) X)
    (smoothG : ∀ s u, ContDiffOn ℝ ∞ (g s u) X)
    (j : ℕ) (err : (s : α) → I s → ℝ) (herr : ∀ s u, 0 ≤ err s u)
    (one : ∀ (l : Fin (j + 1)) (w : Fin l.val → Fin n × Axis), ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ s in F, ∀ u : I s, ‖δ (trace l.val w) (f s u) (point s u) -
        δ (trace l.val w) (g s u) (point s u)‖ ≤ D * err s u) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in F, ∀ (u : I s) (l : Fin (j + 1)),
      ‖iteratedFDeriv ℝ l.val (f s u) (point s u) -
        iteratedFDeriv ℝ l.val (g s u) (point s u)‖ ≤ A * err s u := by
  apply WilsonGraphCartesianJetBound.uniform F j
    (fun s u l => iteratedFDeriv ℝ l.val (f s u) (point s u) -
      iteratedFDeriv ℝ l.val (g s u) (point s u)) err herr
  intro l w
  obtain ⟨D,hD,h⟩ := one l w
  refine ⟨D,hD,?_⟩
  filter_upwards [h] with s hs
  intro u
  change ‖iteratedFDeriv ℝ l.val (f s u) (point s u) (fun i => WilsonGraphCartesianJetBound.axis (w i)) -
    iteratedFDeriv ℝ l.val (g s u) (point s u) (fun i => WilsonGraphCartesianJetBound.axis (w i))‖ ≤ _
  simpa only [onWord hX (smoothF s u) (inside s u) l.val w,
    onWord hX (smoothG s u) (inside s u) l.val w] using hs u

end YM.Integration.GradedFar.AppointedCartesianWords

