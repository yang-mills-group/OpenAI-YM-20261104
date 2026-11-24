import YM.MSbar.Tree.Lift
import YM.Next.RANK.Radian.Indices
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Tree level dimensional prescription: open-tensor lines

We include the `Gamma(1-ε)(x^2)^(ε-1)/(4π^(2-ε))` prescription with the
scale factor `κ^ε` (real dimension parameter neighborhood is sufficient).
This is the standard DR position-space free rule in `D=4-2ε`, uncut IR,
with scaleless self-pair contacts to be deleted. Unlike at positive order
we can use it directly on separated positions; there are neither integrated
interaction vertices here nor pole-regulated operators to be substituted
here. In particular it also applies with Landau convention: the
longitudinal xx piece is absent BEFORE evaluating these curl lines. This
file uses that rule as the definition, not obtaining a Fourier-transform
identity. We prove its analyticity in the real parameter and its collapse
to the normalization and comparison of the YM project, taking arbitrary
jets at distinct positions. Open Lorentz tensor indices for each jet and
curl remain through evaluation at 4 (no evanescent projection before a
pole subtraction).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tree
open Function Set Filter Maxwell Tensor Analysis
open Next.Rank.Radian Next.Rank.Beamer Next.Rank.Prayer
open scoped Classical Topology BigOperators ContDiff

variable {G : Gauge} {k l n : ℕ}
private theorem gamma_cd {x : ℝ} (hx : 0<x) : ContDiffAt ℝ ω Real.Gamma x := by
  have he : AnalyticAt ℂ Complex.Gamma (x:ℂ) := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [Complex.continuous_re.continuousAt.eventually (lt_mem_nhds (show 0<(x:ℂ).re from hx))] with i hi
    refine Complex.differentiableAt_Gamma _ (fun n h=> ?_)
    rw [h] at hi; simp at hi; linarith [Nat.cast_nonneg (α:=ℝ) n]
  exact Complex.reCLM.contDiff.contDiffAt.comp x ((show AnalyticAt ℝ Complex.Gamma (x:ℂ) from he.restrictScalars).contDiffAt.comp (f := fun t : ℝ => (t:ℂ)) x Complex.ofRealCLM.contDiff.contDiffAt)

def volumeFactor (μ ε : ℝ) := (Real.exp Real.eulerMascheroniConstant * μ^2 / (4*Real.pi))^ε

def continued (μ ε : ℝ) (z : E4) := volumeFactor μ ε *
  (Real.Gamma (1-ε)/(4 * Real.pi^(2-ε))) * (‖z‖^2)^(ε-1)

theorem continued_at_four (μ) : continued μ 0= Green := by
  ext1 z
  simp [continued,volumeFactor, Green,normal,Real.rpow_neg (sq_nonneg (‖z‖))]

variable (μ ε : ℝ) (a : Component G k) (b : Component G l) (z : E4)

/-- Degree data for spatial Taylor/curl operations. -/
def native (a : Component G k) : Next.Rank.Beamer.Degree G := ⟨a.1,a.2.2,0,k,a.2.1⟩

/-- Evaluate the two curls of the continued free propagator, with
all partials specified at the two marked points. `z=x-y`, so include
`(-1)^l` also for the opposite-endpoint derivative.
-/
def line : ℂ := paints (native a) (native b)
   (fun i j y => (↑(dV (raypath (native a) (native b) ++ [i,j]) (continued μ ε) y):ℂ)) z

theorem continued_cd (ht : 0<μ) (he : ε<1) (h : z∈ Maxwell.away) :
    ContDiffAt ℝ ω (fun q : ℝ×E4 => continued μ q.1 q.2) (ε,z) := by
  have hz : z≠0 := h
  have hw : ContDiffAt ℝ ω (fun q : ℝ×E4 => ‖q.2‖^2) (ε,z) := (contDiff_norm_sq ℝ).contDiffAt.comp _ contDiffAt_snd
  have hg : ContDiffAt ℝ ω (fun q : ℝ×E4 => Real.Gamma (1-q.1)) (ε,z) :=
    (gamma_cd (show 0<1-ε by linarith)).comp (ε,z) (f:= fun q => 1-q.1) (contDiffAt_const.sub contDiffAt_fst)
  have hh : ContDiffAt ℝ ω (fun q : ℝ×E4 => Real.pi^(2-q.1)) (ε,z) :=
    contDiffAt_const.rpow (contDiffAt_const.sub contDiffAt_fst) Real.pi_pos.ne'
  have hf : ContDiffAt ℝ ω (fun q : ℝ×E4 => 4*Real.pi^(2-q.1)) (ε,z) := contDiffAt_const.mul hh
  exact ((contDiffAt_const.rpow contDiffAt_fst (show Real.exp Real.eulerMascheroniConstant * μ^2/(4*Real.pi) ≠0 by positivity)).mul
    (hg.div hf (show (4 * Real.pi^(2-ε)) ≠ 0 by positivity))).mul
      (hw.rpow (contDiffAt_fst.sub contDiffAt_const) (pow_ne_zero _ (norm_ne_zero_iff.mpr hz)))

private theorem iter_grad {F : ℝ → E4 → ℝ} (i : List Axis)
    (h : ContDiffAt ℝ ω (fun q : ℝ×E4 => F q.1 q.2) (ε,z)) :
    ContDiffAt ℝ ω (fun q : ℝ×E4 => dV i (F q.1) q.2) (ε,z) := by
  induction i with
  | nil => exact h
  | cons a l ih =>
    let f := fun x : ℝ×E4 => fun y : E4=> dV l (F x.1) y
    have hv : ContDiffAt ℝ ω (Function.uncurry f) ((ε,z),z) :=
      ih.comp ((ε,z),z) (f:= fun w => (w.1.1,w.2)) ((contDiffAt_fst.comp (f := Prod.fst) _ contDiffAt_fst).prodMk contDiffAt_snd)
    exact (ContDiffAt.fderiv (g := Prod.snd) (x₀ := (ε,z)) hv contDiffAt_snd le_top).clm_apply contDiffAt_const

theorem line_analytic (ht : 0<μ) (he : ε<1) (h : z∈ Maxwell.away) :
    ContDiffAt ℝ ω (fun q : ℝ×E4 => line μ q.1 a b q.2) (ε,z) := by
  have hu (i j : Axis) : ContDiffAt ℝ ω (fun q : ℝ×E4 => (↑(dV (raypath (native a) (native b) ++ [i,j]) (continued μ q.1) q.2) : ℂ)) (ε,z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (iter_grad _ _ _ (continued_cd _ _ _ ht he h))
  let f (i j : Axis) (e : ℝ) := fun x : E4 => (↑(dV (raypath (native a) (native b) ++ [i,j]) (continued μ e) x) : ℂ)
  have hr (i j x y : Axis) : ContDiffAt ℝ ω (fun q : ℝ×E4 => (if x=y then f i j q.1 else 0) q.2) (ε,z) := by
    split_ifs; exact hu i j; exact contDiffAt_const
  unfold line paints
  split
  · let i:=a.1.val.1;let j:=a.1.val.2; let x:=b.1.val.1;let y:=b.1.val.2
    exact (((hr i y x j).sub (hr i x y j)).sub ((hr j y x i).sub (hr j x y i))).const_smul ((-1:ℂ)^l)
  exact contDiffAt_const

theorem line_zero (hz : z ≠ 0) : line μ 0 a b z = gleam (native a) (native b) z := by
  simp_rw [line, continued_at_four]
  exact contact _ _ _ hz

theorem gleam_pair (hz : z∈Maxwell.away) : gleam (native a) (native b) z = Maxwell.pairing hz (readComponent a) (readComponent b) := by
  unfold readComponent
  rw [map_smul,map_smul,LinearMap.smul_apply, Maxwell.raw_mixed _ _ _ _ _ _ _ _ hz]; unfold gleam native
  split <;> simp [*,smul_eq_mul]; ring

/-- D-dim covariance on compiled MS slots. -/
def compiled (μ ε : ℝ) (i j : Slot G) (z : E4) :=
  ∑ a : Component G i.1, ∑ b : Component G j.1,
    ((matrix i a : ℝ) * matrix j b : ℝ) • line μ ε a b z

theorem compiled_cd (ht : 0<μ) (he : ε<1) (i j : Slot G) (h : z∈ Maxwell.away) :
    ContDiffAt ℝ ω (fun q : ℝ×E4 => compiled μ q.1 i j q.2) (ε,z) :=
  ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => (line_analytic _ _ a b _ ht he h).const_smul (matrix i a * matrix j b)))

lemma compiled_four (i j : Slot G) (hz : z∈ Maxwell.away) : compiled μ 0 i j z=legKernel (coordinateLeg i) (coordinateLeg j) z := by
  simp_rw [compiled,line_zero _ _ _ _ hz,gleam_pair _ _ _ hz]
  let g:= Maxwell.pairing (G:=G) (j:=i.1) (l:=j.1) hz
  rw [show legKernel _ _ z=g (coordinateLeg i) (coordinateLeg j) from rfl,lift_projects i,lift_projects j]
  simp_rw [map_sum g, LinearMap.sum_apply, map_sum (g _), map_smul g, LinearMap.smul_apply, map_smul, smul_eq_mul,Complex.ofReal_sum]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
  simp only [Complex.real_smul]; push_cast
  ring

end YM.MSbar.Tree
