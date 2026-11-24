import YM.Integration.ActualLeadingSeries
import YM.Integration.ActualStencilAnalytic
import YM.MS.Cylinder.Ink
import YangMills.WilsonProof.NativeSupport.YM.MS.Book.Mask
import YM.Analysis.SmoothJets

/-! Original calibrated Wilson sections are analytic in the full link chart.
Their proved coupling valuation annihilates every mixed derivative below the
original grade, not merely the diagonal/radial derivatives. This is the actual
mark input needed by the finite-MS `Allowed` interface; no mark regularity or
low-order vanishing is added as an assumption. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStencilJetFloor
open Function Lattice Wilson RG Source PowerSeries
open RG06 RG06.WilsonCompiler
open MS.Cylinder MS.Cylinder.Taylor MS.Book
open PertExtension.Series
open scoped BigOperators Classical ContDiff

section Taylor
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The native list derivative convention agrees with the actual mixed
Fréchet derivative. The analytic hypothesis is on the same function. -/
theorem ink_ofFn (e : A → E) {f : E → ℝ} (hf : germ f)
    (n : ℕ) (a : Fin n → A) :
    ink e f (List.ofFn a) =
      (iteratedFDeriv ℝ n f 0 (fun i => e (a i)) : ℂ) := by
  induction n generalizing f with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [List.ofFn_succ]
    change ink e (layer (e (a 0)) f) (List.ofFn (fun i => a i.succ)) = _
    rw [ih (germ_layer hf _)]
    congr 1
    have ha : (fun i => e (a i)) =
        Fin.cons (e (a 0)) (fun i => e (a i.succ)) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [ha, Analysis.cons_inner (hf.of_le le_top)]
    rfl

/-- Polarization turns the original radial valuation into a full tensor
valuation, including all mixed derivatives and rank zero. -/
theorem mixed_zero_of_radial {f : E → ℝ} (hf : germ f) (n : ℕ)
    (hz : ∀ u, Radial.jet f n u = 0) :
    iteratedFDeriv ℝ n f 0 = 0 := by
  apply Tensor.ext_diag _ _ (Analysis.sym_Jet (hf.of_le le_top))
    (by intro v s; rfl)
  funext u
  have hu := hz u
  change (n.factorial : ℝ)⁻¹ *
    iteratedFDeriv ℝ n f 0 (fun _ => u) = 0 at hu
  exact (mul_eq_zero.mp hu).resolve_left (inv_ne_zero (by positivity))

/-- Any family of real directions, including the physical bosonic and
zero ghost directions, inherits the same original lower grade. -/
theorem ink_from_radial (e : A → E) {f : E → ℝ} (hf : germ f) (d : ℕ)
    (hz : ∀ n, n < d → ∀ u, Radial.jet f n u = 0) :
    From (ink e f) (d : ℤ) := by
  intro l hl
  have hn : l.length < d := by exact_mod_cast hl
  have hi := ink_ofFn e hf l.length l.get
  rw [List.ofFn_get] at hi
  rw [hi, mixed_zero_of_radial hf _ (hz _ hn)]
  simp
end Taylor

variable {G : Gauge} (C : Family G) (N p d : ℕ)

/-- The full unrestrained link chart, retaining the original calibration,
engineering factor and physical section. -/
def chart (v : C.label d) (x : Site (C.side N p))
    (A : Directions G (C.side N p)) : ℂ :=
  C.O N p v x (increment 1 A)

def realChart (x : Site (C.side N p)) (i : (C.labels.level d).Index)
    (A : Directions G (C.side N p)) : ℝ :=
  (chart C N p d
    (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)) x A).re

theorem chart_analytic (v : C.label d) (x : Site (C.side N p)) :
    ContDiff ℝ ω (chart C N p d v x) := by
  unfold chart
  simp_rw [Dict06.Actual.names]
  exact contDiff_const.mul (ActualStencilAnalytic.polynomial x
    ((C.localSection d).evalC (Dict06.Actual.matrix C N p d v)) 1)

theorem realChart_analytic (x : Site (C.side N p))
    (i : (C.labels.level d).Index) :
    ContDiff ℝ ω (realChart C N p d x i) :=
  Complex.reCLM.contDiff.comp (chart_analytic C N p d _ x)

/-- Vanishing is derived from the actual chosen section's original grade. -/
theorem film_below (hV : Bid.pop (C.localSection d))
    (x : Site (C.side N p)) (i : (C.labels.level d).Index)
    (k : ℕ) (hk : k < ((C.labels.level d).grades i).2) :
    coeff k (physicalFilm C N p d x
      (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) = 0 := by
  rw [physicalFilm_periodize, PowerSeries.coeff_map, physicalCoverFilm,
    Dict06.Actual.meet, (C.labels.level d).coords_basis, PowerSeries.coeff_C_mul,
    markTop_coeff_casing, Tokens.doesNotStart (C.localSection d) hV i k hk,
    mul_zero, map_zero]

theorem realChart_radial_below (hV : Bid.pop (C.localSection d))
    (x : Site (C.side N p)) (i : (C.labels.level d).Index)
    (k : ℕ) (hk : k < ((C.labels.level d).grades i).2)
    (A : Directions G (C.side N p)) :
    Radial.jet (realChart C N p d x i) k A = 0 := by
  let v := Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)
  let f : ℝ → ℂ := fun t => C.O N p v x (roll A t)
  have hr : ∀ t : ℝ, increment (1 : Config G (C.side N p)) (t • A) = roll A t := by
    intro t
    funext e
    simp [increment, roll]
  have hf : ContDiff ℝ ω f := by
    have h := (chart_analytic C N p d v x).comp
      (contDiff_id.smul contDiff_const : ContDiff ℝ ω (fun t : ℝ => t • A))
    change ContDiff ℝ ω (fun t : ℝ => chart C N p d v x (t • A)) at h
    simpa only [chart, hr] using h
  have hzero : Dict06.Series.ordinary k f = 0 := by
    have h := physicalFilm_coefficient C N p d x v A k
    rw [film_below C N p d hV x i k hk, map_zero] at h
    exact h.symm
  have hreal : (fun t : ℝ => realChart C N p d x i (t • A)) =
      Complex.reCLM ∘ f := by
    funext t
    simp only [realChart, chart, hr, comp_apply]
    rfl
  rw [Radial.homogeneous_derivative _ A k
    ((realChart_analytic C N p d x i).contDiffAt.of_le le_top)]
  change Dict06.Series.ordinary k (fun t : ℝ => realChart C N p d x i (t • A)) = 0
  rw [hreal, Dict06.Series.ordinary_map f k (hf.contDiffAt.of_le le_top) Complex.reCLM,
    hzero, map_zero]

/-- The original section supplies every mixed low-order coefficient, with
no covariance, tree, gauge choice or extra mark assumption. -/
theorem realChart_low {A : Type*} (e : A → Directions G (C.side N p))
    (hV : Bid.pop (C.localSection d)) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) :
    From (ink e (realChart C N p d x i)) (((C.labels.level d).grades i).2 : ℤ) :=
  ink_from_radial e (realChart_analytic C N p d x i).contDiffAt _
    (realChart_radial_below C N p d hV x i)

/-- Restricting the same original field to any specified linear chart
preserves this proved grade; the native inversion chart is such a map. -/
theorem realChart_low_comp {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] Directions G (C.side N p)) (e : A → E)
    (hV : Bid.pop (C.localSection d)) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) :
    From (ink e (realChart C N p d x i ∘ L)) (((C.labels.level d).grades i).2 : ℤ) := by
  rw [ink_ctrl_one e L (realChart_analytic C N p d x i).contDiffAt]
  exact realChart_low C N p d (L ∘ e) hV x i

end YM.Integration.ActualStencilJetFloor
