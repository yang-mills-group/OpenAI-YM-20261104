import YM.WilsonMS.Stencil.PanelTest
/-!
# Continuum curvature on smooth sections

Use only point germs at the anchor. Show that the smooth data used in the
stencil jet proof are evaluated from ordinary continuum `F, ∇`
with these signs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.PlaneGauge
open Function Filter Set MeasureTheory
open Analysis Tensor Curves TaylorRules TPath Source Paths RGerm
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
local notation "R" => Gauge.Mat G

abbrev AtG (G : Gauge) :=
  E4 → G.Color

abbrev VectorA (G : Gauge) :=
  Axis → AtG G
variable {A B : VectorA G} {W : Paths.Family G} {P Q : AtG G} {x : E4} {n : ℕ}

def dValue (A : VectorA G) (X : AtG G) (a : Axis) : AtG G := fun x =>
  D (basis a) X x + G.ad (A a x) (X x)

def field (A : VectorA G) (a b : Axis) : AtG G := fun x =>
  D (basis a) (A b) x - D (basis b) (A a) x + G.ad (A a x) (A b x)

def direction (A : VectorA G) (u : E4) (X : AtG G) : AtG G := fun x =>
  ∑ i : Axis, u i • dValue A X i x

def powers (A : VectorA G) (a b : Axis) (u : E4) (n : ℕ) : AtG G :=
  (direction A u)^[n] (field A a b)

abbrev Regular (A : VectorA G) (x : E4) :=
  ∀ i, ContDiffAt ℝ ∞ (A i) x

lemma bracket_smooth (h : ContDiffAt ℝ ∞ P x) (he : ContDiffAt ℝ ∞ Q x) :
    ContDiffAt ℝ ∞ (fun x => G.ad (P x) (Q x)) x := by
  have ht : ContDiffAt ℝ ∞ (fun x => G.colorMat (P x)) x :=
    G.colorMat.toContinuousLinearMap.contDiff.contDiffAt.comp _ h
  have hp : ContDiffAt ℝ ∞ (fun x => G.colorMat (Q x)) x :=
    G.colorMat.toContinuousLinearMap.contDiff.contDiffAt.comp _ he
  exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp _ ((ht.mul hp).sub (hp.mul ht))

lemma field_s (h : Regular A x) (a b : Axis) : ContDiffAt ℝ ∞ (field A a b) x :=
  ((dSmooth (h _) _ (by simp)).sub (dSmooth (h _) _ (by simp))).add (bracket_smooth (h _) (h _))

lemma cov_s (h : Regular A x) (he : ContDiffAt ℝ ∞ P x) (a : Axis) :
    ContDiffAt ℝ ∞ (dValue A P a) x :=
  (dSmooth he _ (by simp)).add (bracket_smooth (h _) he)

lemma powers_s (h : Regular A x) (a b : Axis) (u : E4) : ContDiffAt ℝ ∞ (powers A a b u n) x := by
  induction n with
  | zero => exact field_s h a b
  | succ j ih =>
    rw [powers, iterate_succ_apply']
    exact
      ContDiffAt.sum (f := fun (i : Axis) x => u i • dValue A (powers A a b u j) i x)
        (fun i _ => (cov_s h ih i).const_smul _)

structure Carries (U : E4 → G.Mat) (A B : VectorA G) : Prop where
  eqn (i : Axis) :
    ∀ᶠ y in 𝓝 (0 : E4), G.colorMat (B i y) * U y + D (basis i) U y = U y * G.colorMat (A i y)
variable {U : E4 → G.Mat}

def transforms (U : E4 → G.Mat) (A B : AtG G) :=
  ∀ᶠ y in 𝓝 (0 : E4), G.colorMat (B y) * U y = U y * G.colorMat (A y)

private lemma Dc {P : AtG G} (v : E4) {x : E4} (h : DifferentiableAt ℝ P x) :
    D v (G.colorMat ∘ P) x = G.colorMat (D v P x) :=
  congr_arg (fun f : E4 →L[ℝ] G.Mat => f v)
    (G.colorMat.toContinuousLinearMap.hasFDerivAt.comp _ h.hasFDerivAt).fderiv

private lemma productD {A : Type} [NormedRing A] [NormedAlgebra ℝ A] {u v : E4 → A} (p : E4)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    D p (u * v) x = D p u x * v x + u x * D p v x := by
  unfold D
  rw [(hu.hasFDerivAt.mul' hv.hasFDerivAt).fderiv]
  exact add_comm ..

private lemma exchange {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : E4 → X}
    (h : ContDiffAt ℝ (↑(2 : ℕ)) f x) (u v : E4) : D u (D v f) x = D v (D u f) x := by
  have he (u v : E4) : iteratedFDeriv ℝ 2 f x (Fin.cons u fun _ => v) = D u (D v f) x := by
    rw [cons_jet h]
    unfold D
    simp only [iteratedFDeriv_one_apply]
  rw [← he, cons_inner h]
  simp only [iteratedFDeriv_one_apply]
  rfl

lemma curvature_law (hf : Regular A 0) (hg : Regular B 0) (h : ContDiffAt ℝ ∞ U 0)
    (he : Carries U A B) (a b : Axis) : transforms U (field A a b) (field B a b) := by
  let P (i : Axis) := G.colorMat ∘ A i
  let X (i : Axis) := G.colorMat ∘ B i
  let L (i : Axis) := D (basis i) U
  have ep (i : Axis) : (X i * U + L i) =ᶠ[𝓝 (0 : E4)] U * P i := he.eqn i
  have hw := (contDiffAt_infty.mp h 2).eventually (by simp)
  have ef := eventually_all.mpr (fun i => ((contDiffAt_infty.mp (hf i) 1).eventually (by simp)))
  have eg := eventually_all.mpr (fun i => ((contDiffAt_infty.mp (hg i) 1).eventually (by simp)))
  filter_upwards [hw, ef, eg, eventually_all.mpr (ep),
    eventually_all.mpr (fun i => (ep i).fderiv (𝕜 := ℝ))] with y hy hF hG hh hp
  let c := U y
  have du := hy.differentiableAt (by simp)
  let dp (i : Axis) := (hF i).differentiableAt (by simp)
  let db (i : Axis) := (hG i).differentiableAt (by simp)
  have dP (i : Axis) : DifferentiableAt ℝ (P i) y :=
    G.colorMat.toContinuousLinearMap.differentiableAt.comp _ (dp i)
  have dX (i : Axis) : DifferentiableAt ℝ (X i) y :=
    G.colorMat.toContinuousLinearMap.differentiableAt.comp _ (db i)
  have dL (i : Axis) : DifferentiableAt ℝ (L i) y :=
    (dSmooth hy _ (m := 1) (by norm_cast)).differentiableAt one_ne_zero
  have twist (i : Axis) : X i y * c = c * P i y - L i y := eq_sub_of_add_eq (hh i)
  have anti (i j : Axis) :
    D (basis i) (X j) y * c =
      L i y * P j y + c * D (basis i) (P j) y - D (basis i) (L j) y - X j y * L i y := by
    have hx := DFunLike.congr_fun (hp j) (basis i)
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
    rw [← productD (basis i) du (dP j), ← productD (basis i) (dX j) du]
    have he := congr_arg (fun T : E4 →L[ℝ] G.Mat => T (basis i)) (fderiv_add ((dX j).mul du) (dL j))
    exact he.symm.trans hx
  unfold field
  rw [map_add, map_add, map_sub, map_sub, G.colorMat_ad, G.colorMat_ad]
  rw [← Dc (basis a) (db b), ← Dc (basis b) (db a), ← Dc (basis a) (dp b), ← Dc (basis b) (dp a)]
  change
    (D (basis a) (X b) y - D (basis b) (X a) y + (X a y * X b y - X b y * X a y)) * c =
      c * (D (basis a) (P b) y - D (basis b) (P a) y + (P a y * P b y - P b y * P a y))
  rw [add_mul, sub_mul, anti a b, anti b a, sub_mul, mul_assoc (X a y), mul_assoc (X b y), twist a,
    twist b, mul_sub, mul_sub, ← mul_assoc (X a y) c, ← mul_assoc (X b y) c, twist a, twist b,
    show D (basis a) (L b) y = D (basis b) (L a) y from exchange hy _ _]
  noncomm_ring

lemma derivative_law (hf : ContDiffAt ℝ ∞ P 0) (hg : ContDiffAt ℝ ∞ Q 0) (h : ContDiffAt ℝ ∞ U 0)
    (he : Carries U A B) (hp : transforms U P Q) (a : Axis) :
    transforms U (dValue A P a) (dValue B Q a) := by
  let R' := G.colorMat ∘ P
  let V := G.colorMat ∘ Q
  have ha : V * U =ᶠ[𝓝 0] U * R' := hp
  filter_upwards [ha, ha.fderiv (𝕜 := ℝ), (hf.of_le (m := 1) (by simp)).eventually (by simp),
    (hg.of_le (m := 1) (by simp)).eventually (by simp),
    (h.of_le (m := 1) (by simp)).eventually (by simp), he.eqn a] with y hy ht hP hQ hx hw
  let c := U y
  let L := G.colorMat (B a y)
  let M := G.colorMat (A a y)
  have dU := hx.differentiableAt one_ne_zero
  have dP := hP.differentiableAt one_ne_zero
  have dQ := hQ.differentiableAt one_ne_zero
  let δ := D (basis a) U y
  have hf := DFunLike.congr_fun ht (basis a)
  change D (basis a) (V * U) y = D (basis a) (U * R') y at hf
  have hdV : DifferentiableAt ℝ V y := G.colorMat.toContinuousLinearMap.differentiableAt.comp _ dQ
  have hdR : DifferentiableAt ℝ R' y := G.colorMat.toContinuousLinearMap.differentiableAt.comp _ dP
  have hF := ((productD (basis a) hdV dU).symm.trans hf).trans (productD (basis a) dU hdR)
  change D (basis a) V y * c + V y * δ = δ * R' y + c * D (basis a) R' y at hF
  change V y * c = c * R' y at hy
  have hh : L * c = c * M - δ := eq_sub_of_add_eq hw
  unfold dValue
  rw [map_add, map_add, G.colorMat_ad, G.colorMat_ad, ← Dc _ dP, ← Dc _ dQ]
  change (D (basis a) V y + (L * V y - V y * L)) * c = c * (D (basis a) R' y + (M * R' y - R' y * M))
  rw [add_mul, eq_sub_of_add_eq hF, sub_mul, mul_assoc L, mul_assoc (V y), hh, hy, ← mul_assoc L c,
    hh, mul_sub (V y), ← mul_assoc (V y) c, hy]
  noncomm_ring

lemma powers_law (hf : Regular A 0) (hg : Regular B 0) (h : ContDiffAt ℝ ∞ U 0) (he : Carries U A B)
    (a b : Axis) (x : E4) : transforms U (powers A a b x n) (powers B a b x n) := by
  induction n with
  | zero => exact curvature_law hf hg h he a b
  | succ j ih =>
    filter_upwards [eventually_all.mpr fun i =>
        derivative_law (powers_s hf a b x) (powers_s hg a b x) h he ih i] with
      y hy
    rw [powers, powers, iterate_succ_apply', iterate_succ_apply']
    unfold direction
    rw [map_sum, map_sum, Finset.sum_mul, Finset.mul_sum]
    exact
      Finset.sum_congr rfl fun i _ => by
        rw [map_smul, map_smul, mul_smul_comm, smul_mul_assoc]
        exact congr_arg (x i • ·) (hy i)

abbrev voiced (B : Paths.Family G) (a : ℝ) : VectorA G := fun i x => B i (a, x)

def dialed (B : Paths.Family G) (a : ℝ) : E4 → G.Mat := fun x => reprQ B (a, x)

lemma sings (h : Flow W) (a : ℝ) : Regular (voiced W a) 0 := fun i =>
  (h _ |>.comp (show ContDiff ℝ ∞ (fun x : E4 => (a, x)) from by fun_prop)).contDiffAt

lemma dials (h : Flow W) (a : ℝ) : Carries (dialed W a) (voiced W a) (voiced (RGerm.pull W) a) := by
  constructor
  intro i
  have ht := (repr_smooth (a := a) h).of_le (m := 1) (by simp) |>.eventually (by simp)
  filter_upwards [((continuous_const.prodMk continuous_id).tendsto (0 : E4)).eventually ht] with x hx
  let V := reprQ W
  let X := (a, x)
  have he : DifferentiableAt ℝ V X := hx.differentiableAt one_ne_zero
  have hh : D (basis i) (dialed W a) x = D (d i) V X := by
    let T (y : E4) : Domain := (a, y)
    have ht : HasFDerivAt T (ContinuousLinearMap.inr ℝ ℝ E4) x :=
      (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
    exact DFunLike.congr_fun (he.hasFDerivAt.comp x ht).fderiv _
  change reprA (RGerm.pull W) _ X * V X + D (basis i) (dialed W a) x = V X * reprA W i X
  rw [hh, formula he]
  unfold rightL
  change (_ * star (V X) - D (d i) V X * star (V X)) * V X + _ = _
  rw [sub_mul, mul_assoc (_ * _ : G.Mat), mul_assoc (D (d i) V X),
    show star (V X) * V X = 1 from G.mat_star_mul _, mul_one, mul_one, sub_add_cancel]

lemma at_anchor (h : Flow W) (x y : Axis) (z : E4) (k : ℕ) (a : ℝ) :
    powers (voiced (RGerm.pull W) a) x y z k 0 = powers (voiced W a) x y z k 0 := by
  have ht : Regular (voiced (RGerm.pull W) a) 0 := fun i => pulseS h i
  have hp :=
    powers_law (n := k) (sings h a) ht
      (show ContDiffAt ℝ ∞ (dialed W a) 0 from
        (repr_smooth h).comp (f := fun x : E4 => (a, x)) _ (by fun_prop))
      (dials h a) x y z
  unfold transforms at hp
  have hc := hp.self_of_nhds
  rw [show dialed W a 0 = 1 from
      (by
        unfold dialed reprQ
        rw [comp_apply, based_center h]
        rfl),
    mul_one, one_mul] at hc
  exact G.colorMat_injective hc
end YM.WilsonMS.PlaneGauge
