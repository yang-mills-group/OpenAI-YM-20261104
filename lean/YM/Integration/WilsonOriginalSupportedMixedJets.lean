import YM.Integration.WilsonOriginalSupportedBoxChart
import YM.Integration.WilsonOriginalMixedFourierRead

/-! Each successive coordinate variation is taken on the actual compact
field before its periodic Fourier read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSupportedMixedJets
open Set Filter Finset UnitAddTorus
open WilsonOriginalSupportedBoxChart
open WilsonOriginalPhysicalBoxSlices (positions)
open scoped Topology ContDiff Interval BigOperators

def derivative {d : ℕ} (dir : ℕ → Fin d) (f : Space d → ℂ) : ℕ → Space d → ℂ
  | 0 => f
  | k+1 => fun x => fderiv ℝ (derivative dir f k) x (Pi.single (dir k) (1:ℝ))

theorem smooth {d : ℕ} (dir : ℕ → Fin d) {f : Space d → ℂ} (sf : ContDiff ℝ ∞ f)
    (j : ℕ) : ContDiff ℝ ∞ (derivative dir f j) := by
  induction j with
  | zero => exact sf
  | succ k ih => exact (ih.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

theorem support {d : ℕ} (dir : ℕ → Fin d) {l h : Space d} {f : Space d → ℂ}
    (sf : Supported l h f) (j : ℕ) : Supported l h (derivative dir f j) := by
  induction j with
  | zero => exact sf
  | succ k ih =>
    intro i x hx
    have ext : (fun z : Space d => z i) ⁻¹' (Icc (l i) (h i))ᶜ ∈ 𝓝 x :=
      (isClosed_Icc.isOpen_compl.preimage (continuous_apply i)).mem_nhds hx
    have zero : derivative dir f k =ᶠ[𝓝 x] (fun _ => (0:ℂ)) := by
      filter_upwards [ext] with y hy using ih i y hy
    change (fderiv ℝ (derivative dir f k) x) _ = 0
    rw [zero.fderiv_eq,fderiv_const_apply]
    rfl

def field {d : ℕ} (dir : ℕ → Fin d) {l h : Space d} (left : ∀ i, 0 < l i)
    (right : ∀ i, h i < 1) (f : Space d → ℂ) (sf : ContDiff ℝ ∞ f)
    (hold : Supported l h f) (k : ℕ) : C(UnitAddTorus (Fin d),ℂ) :=
  ⟨read (derivative dir f k),continuous_read (support dir hold k) left right
    (smooth dir sf k).continuous.continuousOn⟩

theorem slice {d : ℕ} (i : Fin (d+1)) {l h : Space (d+1)} {g : Space (d+1) → ℂ}
    (left : ∀ i, 0 < l i) (right : ∀ i, h i < 1) (hold : Supported l h g)
    (rest : Fin d → UnitAddCircle) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (sg : ContDiff ℝ ∞ g) :
    HasDerivAt (fun t : ℝ => read g (i.insertNth (t:UnitAddCircle) rest))
      (fderiv ℝ g (positions i 0 rest x) (Pi.single i (1:ℝ))) x := by
  have expression (t : ℝ) : positions i 0 rest t =
      positions i 0 rest 0+t • Pi.single i (1:ℝ) := by
    simpa using WilsonOriginalCompactAxisExpense.moved i 0 rest 0 t
  have line : HasDerivAt (positions i 0 rest) (Pi.single i (1:ℝ)) x := by
    rw [show positions i 0 rest = (fun t => positions i 0 rest 0+t • Pi.single i (1:ℝ)) from funext expression]
    simpa using ((hasDerivAt_id x).smul_const (Pi.single i (1:ℝ))).const_add (positions i 0 rest 0)
  exact ((sg.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt x line).congr_of_eventuallyEq
    (WilsonOriginalSupportedBoxChart.original hold left right i rest hx)

theorem original {d : ℕ} (dir : ℕ → Fin (d+1)) {l h : Space (d+1)} (left : ∀ i, 0 < l i)
    (right : ∀ i, h i < 1) (f : Space (d+1) → ℂ) (sf : ContDiff ℝ ∞ f)
    (hold : Supported l h f) (j : ℕ) (v : Fin (d+1) → ℤ) :
    mFourierCoeff (read (derivative dir f j)) v =
      WilsonOriginalLowFourierJets.jet (fun k : Fin j => dir k.val)
        (fun _ => 2*(Real.pi:ℂ)*Complex.I) v*mFourierCoeff (read f) v := by
  apply WilsonOriginalMixedFourierRead.original j dir (field dir left right f sf hold)
  intro k _ rest x hx
  have inBox : x ∈ Icc (0:ℝ) 1 := by simpa [uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] using hx
  have atPoint := (WilsonOriginalSupportedBoxChart.original (support dir hold (k+1)) left right
    (dir k) rest inBox).self_of_nhds
  change HasDerivAt _ (read (derivative dir f (k+1)) _) _
  dsimp only at atPoint
  rw [atPoint]
  exact slice (dir k) left right (support dir hold k) rest inBox (smooth dir sf k)

end YM.Integration.WilsonOriginalSupportedMixedJets
