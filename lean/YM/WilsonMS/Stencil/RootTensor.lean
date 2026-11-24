import YM.WilsonMS.Stencil.MomentumCurvature
/-!
# Rows on real packet capture the MS choice of optics
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Packet
open Function Filter Set MeasureTheory
open Analysis Tensor TPath Source Paths TaylorRules PlaneGauge Panel Extract MS Plane Heat Flux
open Landau Arts Pilot Tone Local.BV Mach Motif Halo Native Koszul
open Complex (I)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {ι : Type} [Fintype ι] (B : ι → PairK G)

def coordTrace (P : Inputs ι → AtG G) (c : G.ColorIndex) := fun x : coordinates ι =>
  (((P x.2 x.1) c : ℝ) : ℂ)

structure Projects (P : Inputs ι → AtG G) (H : Mield G 0) : Prop where
  smooth : Smooth (fun x : coordinates ι => P x.2 x.1)
  rows : ∀ i, AtVertex B (coordTrace P i) (H i)

private lemma bracket_story (A B : G.Color) (a : G.ColorIndex) :
    (((G.ad A B) a : ℝ) : ℂ) =
      ∑ j : G.ColorIndex, ∑ k : G.ColorIndex, rune j k a * ((A j : ℂ) * (B k : ℂ)) := by
  have he (x : G.Color) : ∑ i : G.ColorIndex, x i • Native.baseC i = x := by
    ext
    simp [Native.baseC, Pi.single_apply, mul_ite]
  nth_rw 1 [← he A, ← he B]
  rw [map_sum]
  simp only [map_sum, map_smul]
  push_cast
  unfold rune letterLie
  simp
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring
namespace Projects
variable {B} {H V : Mield G 0} {P Q : Inputs ι → AtG G}

lemma bracket (h : Projects B P H) (hp : Projects B Q V) :
    Projects B (fun z y => G.ad (P z y) (Q z y)) (jaw G 0 H V) := by
  have he :=
    G.projectColor.toContinuousLinearMap.contDiff.comp
      (ContDiff.sub (n := ∞) (f := fun x : coordinates ι =>
        G.colorMat (P x.2 x.1) * G.colorMat (Q x.2 x.1)) (g := fun x =>
        G.colorMat (Q x.2 x.1) * G.colorMat (P x.2 x.1))
        ((G.colorMat.toContinuousLinearMap.contDiff.comp h.smooth).mul
          (G.colorMat.toContinuousLinearMap.contDiff.comp hp.smooth))
        ((G.colorMat.toContinuousLinearMap.contDiff.comp hp.smooth).mul
          (G.colorMat.toContinuousLinearMap.contDiff.comp h.smooth)))
  refine ⟨he, fun i => ?_⟩
  rw [chew]
  let W (j k : G.ColorIndex) := coordTrace P j * coordTrace Q k
  rw [show coordTrace _ i = ∑ j : G.ColorIndex, ∑ k : G.ColorIndex, rune j k i • W j k from ?_]
  · exact
      AtVertex.sum _ fun j _ => AtVertex.sum _ fun k _ => ((h.rows j).product_read (hp.rows k)).smul _
  unfold coordTrace
  funext x
  simp_rw [Finset.sum_apply]
  exact bracket_story _ _ _

lemma actual_seed (B : ι → PairK G) (a : Axis) :
    Projects B (fun z => trial B z a) (Motif.A 0 G (chair 0 a)) :=
  ⟨trial_s B a, AtVertex.seed B a⟩

lemma sum2 (h : Projects B P H) (hp : Projects B Q V) : Projects B (P + Q) (H + V) := by
  refine ⟨h.smooth.add hp.smooth, fun i => ?_⟩
  rw [show coordTrace (P + Q) i = coordTrace P i + coordTrace Q i from
      funext fun x => Complex.ofReal_add ..]
  exact (h.rows i).add (hp.rows i)

lemma subtr (h : Projects B P H) (hp : Projects B Q V) : Projects B (P - Q) (H - V) := by
  refine ⟨h.smooth.sub hp.smooth, fun i => ?_⟩
  rw [show coordTrace (P - Q) i = coordTrace P i - coordTrace Q i from
      funext fun x => Complex.ofReal_sub ..]
  exact (h.rows i).sub (hp.rows i)

lemma scaleR (c : ℝ) (h : Projects B P H) : Projects B (c • P) ((c : ℂ) • H) := by
  refine ⟨h.smooth.const_smul c, fun i => ?_⟩
  rw [show coordTrace (c • P) i = (c : ℂ) • coordTrace P i from funext fun x => Complex.ofReal_mul ..]
  exact (h.rows i).smul _

lemma dir (h : Projects B P H) (a : Axis) :
    Projects B (fun z y => Analysis.D (basis a) (P z) y) (axisP (chair 0 a) H) := by
  let f (x : coordinates ι) := P x.2 x.1
  have hz (z : Inputs ι) : Smooth (P z) := h.smooth.comp (f := fun y : E4 => (y, z)) (by fun_prop)
  refine ⟨?_, fun i => ?_⟩
  · rw [show
        (fun x : coordinates ι => Analysis.D (basis a) (P x.2) x.1) =
          Analysis.D (basis a, (0 : Inputs ι)) f
        from ?_]
    exact
      contDiff_iff_contDiffAt.mpr fun x =>
        dSmooth (show ContDiffAt ℝ ∞ f x from h.smooth.contDiffAt) _ (by simp)
    funext x
    let L : E4 →L[ℝ] coordinates ι := ContinuousLinearMap.inl ℝ E4 (Inputs ι)
    have ht : HasFDerivAt (fun t : E4 => (t, x.2)) L x.1 :=
      (hasFDerivAt_id x.1).prodMk (hasFDerivAt_const ..)
    exact
      DFunLike.congr_fun
        ((show DifferentiableAt ℝ f (x.1, x.2) from
                h.smooth.differentiable (by simp) x).hasFDerivAt.comp
            x.1 ht).fderiv
        _
  rw [show coordTrace (fun z y => Analysis.D (basis a) (P z) y) i = _ from ?_]
  exact (h.rows i).derive a
  funext x
  let L := Complex.ofRealCLM ∘L EuclideanSpace.proj i (𝕜 := ℝ)
  exact
    Eq.symm
      (DFunLike.congr_fun
        (L.hasFDerivAt.comp (f := P x.2) _ ((hz x.2).differentiable (by simp) x.1).hasFDerivAt).fderiv
        (basis a))
variable (B)

lemma fielded (a b : Axis) :
    Projects B (fun z => PlaneGauge.field (trial B z) a b) (cur 1 (chair 0 a) (chair 0 b)) := by
  rw [cur, one_smul]
  exact
    (((actual_seed B b).dir a).subtr ((actual_seed B a).dir b)).sum2
      ((actual_seed B a).bracket (actual_seed B b))

lemma axis_v (a : Axis) (h : Projects B P H) :
    Projects B (fun z => dValue (trial B z) (P z) a) (convoke 1 (chair 0 a) H) := by
  rw [convoke, LinearMap.add_apply, LinearMap.smul_apply, one_smul]
  exact (h.dir a).sum2 ((actual_seed B a).bracket h)

lemma sum {X : Type} {P : X → Inputs ι → AtG G} {H : X → Mield G 0} (s : Finset X)
    (h : ∀ i ∈ s, Projects B (P i) (H i)) : Projects B (∑ i ∈ s, P i) (∑ i ∈ s, H i) := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨contDiff_const, fun i => ?_⟩
    exact AtVertex.zero _
  | insert a s he ih =>
    rw [Finset.sum_insert he, Finset.sum_insert he]
    exact (h a (Finset.mem_insert_self ..)).sum2 (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma powerF (k : ℕ) (x : E4) (a b : Axis) :
    Projects B (fun z : Inputs ι => PlaneGauge.powers (trial B z) a b x k) (JRad.rayF 1 x a b k) := by
  induction k with
  | zero =>
    rw [JRad.rayF, pow_zero]
    exact fielded B a b
  | succ k ih =>
    let P (z : Inputs ι) := PlaneGauge.powers (trial B z) a b x k
    let K := JRad.rayF 1 x a b k (G := G) (n := 0)
    rw [JRad.rayF, pow_succ']
    simp only [powers, iterate_succ_apply']
    change
      Projects B (fun z : Inputs ι => PlaneGauge.direction (trial B z) x (P z))
        (JRad.direction G 0 1 x K)
    rw [show
        (fun z : Inputs ι => PlaneGauge.direction (trial B z) x (P z)) =
          ∑ i : Axis, (x i : ℝ) • (fun z : Inputs ι => dValue (trial B z) (P z) i)
        from ?_,
      JRad.direction, LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply]
    · exact sum _ _ fun i _ => (axis_v B i ih).scaleR _
    ext1 z
    ext1 y
    rw [Finset.sum_apply, Finset.sum_apply]
    rfl

lemma nodeF (k : ℕ) (x : E4) (a : Axis) :
    Projects B (fun z y => JRad.volume k • ∑ i : Axis, x i • PlaneGauge.powers (trial B z) i a x k y)
      (JRad.node 1 a k x) := by
  let V := ∑ i : Axis, (x i : ℝ) • JRad.rayF 1 x i a k (G := G) (n := 0)
  let P : Inputs ι → AtG G :=
    ∑ i : Axis, (x i : ℝ) • (fun z : Inputs ι => PlaneGauge.powers (trial B z) i a x k)
  have he : Projects B P V := sum _ _ (fun j _ => (powerF B k x j a).scaleR _)
  rw [show
      (fun z : Inputs ι => fun y : E4 =>
          JRad.volume k • ∑ i : Axis, x i • PlaneGauge.powers (trial B z) i a x k y) =
        JRad.volume k • P
      from ?_]
  exact he.scaleR _
  unfold P
  ext1 z
  ext1 y
  simp only [Pi.smul_apply, Finset.sum_apply]
end Projects
section letter

structure AtPoint (F : Inputs ι → ℂ) (H : Rack G 0) : Prop where
  smooth : Smooth F
  reads : ∀ l : List ι, scans cosine sine F l 0 = H (l.map (packet B))
namespace AtPoint
variable {B} {F V : Inputs ι → ℂ} {W H : Rack G 0}

lemma reduce (X : coordinates ι → ℂ) (h : AtVertex B X H) : AtPoint B (fun z => X (0, z)) H := by
  refine ⟨h.smooth.comp (by fun_prop), fun l => ?_⟩
  have he := h.read l 0
  rw [Θ, zero_p, one_mul] at he
  exact he

lemma add (h : AtPoint B F H) (ht : AtPoint B V W) : AtPoint B (F + V) (H + W) := by
  refine ⟨h.smooth.add ht.smooth, fun l => ?_⟩
  rw [sum2 h.smooth ht.smooth, Pi.add_apply, h.reads, ht.reads]
  rfl

lemma smul (h : AtPoint B F H) (c : ℂ) : AtPoint B (c • F) (c • H) := by
  refine ⟨h.smooth.const_smul c, fun l => ?_⟩
  rw [scale_s h.smooth, Pi.smul_apply, h.reads]
  rfl

lemma mul (h : AtPoint B F H) (ht : AtPoint B V W) : AtPoint B (F * V) (bite 0 G H W) :=
  ⟨h.smooth.mul ht.smooth, sc_times _ _ (fun _ => rfl) H W h.smooth ht.smooth h.reads ht.reads⟩

lemma sum {X : Type} {P : X → Inputs ι → ℂ} {H : X → Rack G 0} (s : Finset X)
    (h : ∀ i ∈ s, AtPoint B (P i) (H i)) : AtPoint B (∑ i ∈ s, P i) (∑ i ∈ s, H i) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨contDiff_const, fun l => ?_⟩
    rw [sc_zero]
    rfl
  | insert a s hep ih =>
    rw [Finset.sum_insert hep, Finset.sum_insert hep]
    exact (h a (Finset.mem_insert_self ..)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end AtPoint
variable (a : Labels.Key G)

lemma pay_slot : AtPoint B (fun x => PlaneGauge.moveSlot G (trial B x) a) (JRad.member a 1 0) := by
  have hx (v : PlaneGauge.Probe G) :
    AtPoint B (fun z => (↑((head (trial B z) v.1 v.2.1 a.1) v.2.2) : ℂ))
      (JRad.node 1 v.2.1 a.1 v.1 v.2.2) :=
    AtPoint.reduce _ ((Projects.nodeF B a.1 v.1 v.2.1).rows v.2.2)
  let Z := ray_basis a
  let H (v : PlaneGauge.Probe G) := JRad.factor G a.1 (linear_part G a.1 v)
  let F (v : PlaneGauge.Probe G) := fun z : Inputs ι =>
    (((PlaneGauge.head (trial B z) v.1 v.2.1 a.1) v.2.2 : ℝ) : ℂ)
  have hV (i) : AtPoint B (F i) (H i 1 0) := by
    rw [show H i 1 0 = _ from JRad.corresponding G a.1 i.1 i.2.1 i.2.2 1 0]
    exact hx i
  rw [show JRad.member a 1 0 = ∑ j ∈ Z.support, (Z j : ℝ) • H j 1 0 from ?_,
    show (fun z => PlaneGauge.moveSlot G (trial B z) a) = ∑ i ∈ Z.support, (Z i : ℂ) • F i from ?_]
  · exact AtPoint.sum _ (fun i _ => (hV i).smul (Z i : ℂ))
  · funext z
    unfold PlaneGauge.moveSlot
    simp only [Finsupp.sum, Complex.ofReal_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_mul ..
  unfold JRad.member
  rw [← ray_eq a, Finsupp.sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  rfl

lemma print_readout (p : Labels.Pol G) :
    AtPoint B (fun z => PlaneGauge.unread (trial B z) p) (JRad.optic G p 1 0) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [JRad.constV]
    simp only [PlaneGauge.unread, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    refine ⟨contDiff_const, fun l => ?_⟩
    rw [Extract.const]
    cases l <;> rfl
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p a hp =>
    rw [JRad.productV, JRad.names]
    simp only [map_mul, unread, MvPolynomial.aeval_X]
    exact hp.mul (pay_slot B a)
end letter
end YM.WilsonMS.Packet
