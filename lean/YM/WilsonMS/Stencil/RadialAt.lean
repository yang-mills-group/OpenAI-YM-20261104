import YM.WilsonMS.Stencil.SlideMean
/-!
# Radial gauge near the centre

Rays travel *out*. Keep real path curves. Statements requiring smoothness
near `(a,0)` are germs for each finite order of derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.RGerm
open Function Filter Set MeasureTheory
open Analysis Tensor Curves TaylorRules TPath Source Paths
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
local notation "R" => Gauge.Mat G
local notation "I" => unitInterval

abbrev Domain :=
  ℝ × E4
variable {B : Paths.Family G} {y : Domain} {k : ℕ} {a t : ℝ}

def input (B : Paths.Family G) (x : Domain × ℝ) : G.Color :=
  ∑ i : Axis, x.1.2 i • B i (x.1.1, x.2 • x.1.2)

def radialG (B : Paths.Family G) (x : Domain) : G.El :=
  TPath.track (G := G) (fun t => input B (x, t)) 1

abbrev reprQ (B : Paths.Family G) :=
  G.mat ∘ radialG B

lemma input_s (h : Flow B) : ContDiff ℝ ∞ (input B) := by
  unfold input
  refine ContDiff.sum fun i _ => ?_
  exact
    (show ContDiff ℝ ∞ (fun x : Domain × ℝ => x.1.2 i) from (by fun_prop)).smul
      ((h i).comp (f := fun x : Domain × ℝ => (x.1.1, x.2 • x.1.2)) (by fun_prop))

lemma ray_s (h : Flow B) (x : Domain) : ContDiff ℝ 1 (fun t => input B (x, t)) := by
  exact ((input_s h).of_le (by simp)).comp (by fun_prop)

lemma input_zero : input B ((t, 0), a) = 0 := by simp [input]

lemma repr_smooth (h : Flow B) : ContDiffAt ℝ ∞ (reprQ B) (a, 0) := by
  apply contDiffAt_infty.mpr
  intro k
  exact
    (comparison (p := (a, 0)) (G := G) (fun _ _ => contDiffAt_infty.mp (input_s h |>.contDiffAt) k)
        (fun i _ => input_zero) (ray_s h)).smooth

lemma based_center (h : Flow B) (t : ℝ) : radialG B (t, 0) = 1 := by
  apply G.mat_injective
  have he (v : ℝ) : input B ((t, 0), v) = 0 := input_zero
  have hx :=
    (comparison (p := (t, 0)) (G := G) (fun _ _ => contDiffAt_infty.mp (input_s h |>.contDiffAt) 0)
      (fun i _ => he i) (ray_s h))
  have hm : Curves.along I (input B) (t, 0) = 0 :=
    ContinuousMap.ext fun i =>
      (Curves.path_val (fun _ _ => contDiffAt_infty.mp (input_s h |>.contDiffAt) 0) i).trans (he _)
  exact
    hx.value.trans
      (by
        unfold comp
        rw [hm, step_zero]
        rfl)

lemma scaled_trace (h : Flow B) (a : ℝ) (x : E4) :
    SolvesLink (fun t => radialG B (a, t • x)) (fun t => input B ((a, x), t)) := by
  let u := track (G := G) (fun t => input B ((a, x), t))
  have he : SolvesLink u (fun t => input B ((a, x), t)) := tracks (ray_s h _)
  suffices ht : ∀ s : ℝ, radialG B (a, s • x) = u s by rwa [funext ht]
  intro s
  have hp (t : ℝ) : input B ((a, s • x), t) = s • input B ((a, x), s * t) := by
    unfold input
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [smul_smul, mul_comm t]
  unfold radialG
  rw [← track_form (g := fun t => u (s * t)) (ray_s h (a, s • x))]
  · simp
  refine
    ⟨by
      simp only [mul_zero]
      exact he.1, fun t => ?_⟩
  dsimp only
  rw [hp t, map_smul, mul_smul_comm]
  have ht : HasDerivAt (fun t : ℝ => s * t) s t := by simpa using! (hasDerivAt_id' t).const_mul s
  exact (he.2 (s * t)).scomp t ht

abbrev d (i : Axis) : Domain :=
  (0, basis i)

def reprA (B : Paths.Family G) (i : Axis) (y : Domain) : G.Mat :=
  G.colorMat (B i y)

def rightL (B : Paths.Family G) (v : Domain) (y : Domain) :=
  (D v (reprQ B) y) * star (reprQ B y)

lemma tangent_right (h : DifferentiableAt ℝ (reprQ B) y) (v : Domain) : rightL B v y ∈ G.lie := by
  let s (t : ℝ) := y + t • v
  let f (t : ℝ) := reprQ B (s t) * star (reprQ B y)
  have hv : HasDerivAt s v 0 := by
    simpa only [one_smul, s] using! ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add y
  have he : HasDerivAt f (rightL B v y) 0 :=
    (h.hasFDerivAt.comp_hasDerivAt_of_eq 0 hv (by simp [s])).mul_const _
  refine G.tangent_generates he ?_ ?_
  · simp [f, s, reprQ]
  intro t
  exact
    ⟨radialG B (s t) * (radialG B y)⁻¹,
      (G.mat_mul ..).trans
        (by
          rw [G.mat_inv]
          rfl)⟩

def pull (B : Paths.Family G) : Paths.Family G := fun i x =>
  G.adjoint (radialG B x) (B i x) - G.projectColor (rightL B (d i) x)

lemma formula (h : DifferentiableAt ℝ (reprQ B) y) (i : Axis) :
    reprA (pull B) i y = reprQ B y * reprA B i y * star (reprQ B y) - rightL B (d i) y := by
  unfold reprA pull
  rw [map_sub, G.mat_adjoint, G.colorMat_project_self (tangent_right h _)]
  rfl

lemma pull_s (h : Flow B) (i : Axis) : ContDiffAt ℝ ∞ (pull B i) (a, 0) := by
  have he := repr_smooth (a := a) h
  have hz : ContDiffAt ℝ ∞ (fun x => star (reprQ B x)) (a, 0) :=
    (starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp (f := reprQ B) _ he
  refine
    ContDiffAt.sub (f := fun x => G.adjoint (radialG B x) (B i x)) (g := fun x =>
      G.projectColor (rightL B (d i) x)) ?_ ?_
  · exact
      ContDiffAt.comp (g := G.projectColor) _ G.projectColor.toContinuousLinearMap.contDiff.contDiffAt
        ((he.mul
              (G.colorMat.toContinuousLinearMap.contDiff.contDiffAt.comp (f := B i) _
                (h i |>.contDiffAt))).mul
          hz)
  exact
    G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp (f := rightL B (d i)) _
      ((dSmooth he _ (by simp)).mul hz)

lemma root_free (h : Flow B) : ∀ᶠ x : Domain in 𝓝 (a, 0), ∑ i : Axis, (x.2 i) • pull B i x = 0 := by
  have ht : ContDiffAt ℝ 1 (reprQ B) (a, 0) := (repr_smooth h).of_le (by simp)
  filter_upwards [ht.eventually (by simp)] with x hx
  apply G.colorMat_injective
  rw [map_sum]
  simp_rw [map_smul,
    show ∀ i, G.colorMat (pull B i x) = _ from fun i =>
      formula (y := x) (B := B) (hx.differentiableAt one_ne_zero) i,
    smul_sub, Finset.sum_sub_distrib, map_zero, sub_eq_zero]
  unfold rightL Analysis.D
  simp_rw [← smul_mul_assoc]
  simp_rw [smul_mul_assoc _ (reprQ B x), ← mul_smul_comm _ (reprQ B x), ← Finset.sum_mul, ←
    Finset.mul_sum]
  simp_rw [← map_smul, ← map_sum]
  congr 1
  let V (t : ℝ) : Domain := (x.1, t • x.2)
  have hp : ∑ i : Axis, x.2 i • d i = ((0 : ℝ), x.2) :=
    Prod.ext (by simp [d, Prod.fst_sum])
      (by
        ext
        simp [d, Prod.snd_sum])
  have he : V 1 = x := by simp [V]
  have hv : HasDerivAt V ((0 : ℝ), x.2) 1 := by
    simpa only [V, one_smul] using!
      (hasDerivAt_const (1 : ℝ) x.1).prodMk (((hasDerivAt_id' (1 : ℝ)).smul_const x.2))
  have hu :=
    ((hx.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt_of_eq 1 hv he.symm).unique
      ((scaled_trace h x.1 x.2).2 1)
  rw [hp, hu]
  unfold reprA input
  simp only [map_sum, map_smul, one_smul]
  rfl
end YM.WilsonMS.RGerm
