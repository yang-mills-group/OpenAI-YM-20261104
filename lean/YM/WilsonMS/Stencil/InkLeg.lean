import YM.WilsonMS.Stencil.Sitemap
/-!
# A single label leg at our chosen MS basis

Momentum readout uses MIDPOINT value of link logs. The stencil norms in
XSpace and the off-shell radial jet test use genuine holonomies over edges.
We do NOT assume equality of their jets; prove the conversion in the next file.
Here install the linear readout facts on site slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Webs
open Function Filter Finset Set MeasureTheory XSpace
open Lattice RG Maxwell Source Labels Maxwell.Free Wilson
open MS MS.Local MS.Local.Physical MS.Plane MS.Koszul MS.Theater MS.Tone
open MS.Menus MS.Land MS.Local.BV MS.Cylinder MS.Book MS.Native MS.Puff.Actors MS.Landau.Detect
open MS.Native.Sew MS.Native.Studio MS.Native.Wilsonian MS.Native.Chart MS.Native.Draft
  MS.Cylinder.Lab MS.Cylinder.Taylor
open Work Drops
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {H : Source.Hol G} {p : Labels.Pol G} {d j : ℕ} (A : Survey G H d)
local notation "C" => Edge Cover
local notation "X" => Lot G C

def lit (U : X) (θ : ℝ) : Links ℤ G.El := fun x => G.lieExp (θ • U x)
lemma priced (w : Walk) (U : X) (x : Cover) :
    HasDerivAt (fun s => G.mat (travel (lit U s) x w)) (G.colorMat (Exterior.linkSum U x w)) 0 := by
  have he : lit U 0 = 1 := by
    ext1 i
    simp [lit]
  induction w generalizing x with
  | nil =>
    simp only [travel, Exterior.linkSum, map_zero]
    exact hasDerivAt_const ..
  | cons b w ih =>
    have hv : HasDerivAt (fun t : ℝ => G.mat (lit U t (b.used x))) (G.colorMat (U (b.used x))) 0 := by
      let f := G.mat ∘ G.lieExp
      let g (t : ℝ) := t • U (b.used x)
      have hh : HasDerivAt g (U (b.used x)) 0 := by
        simpa only [one_smul] using! (hasDerivAt_id' (0 : ℝ)).smul_const (U (b.used x))
      have hF : HasFDerivAt f G.colorMat.toContinuousLinearMap (g 0) := by
        rw [show g (0 : ℝ) = 0 from zero_smul _ _]
        exact G.expDiff_zero
      exact hF.comp_hasDerivAt (f := g) _ hh
    have hp :
      HasDerivAt (fun θ => G.mat (b.read (lit U θ) x))
        (G.colorMat (if b.neg then -U (b.used x) else U (b.used x))) 0 := by
      unfold Step.read
      split
      · rw [map_neg, ← G.colorMat_skew]
        simp only [G.mat_inv]
        exact hv.star
      exact hv
    have hz : b.read (lit U 0) x = 1 := by
      unfold Step.read
      rw [he]
      split <;> simp
    simp_rw [travel, G.mat_mul]
    apply (hp.mul (ih _)).congr_deriv
    simp only [he, show b.read (1 : Links ℤ G.El) x = 1 from he ▸ hz, Pressure.one, G.mat_one,
      one_mul, mul_one, Exterior.linkSum, map_add]

def CurlOn (s : Slot) (U : X) :=
  Exterior.linkSum U s.offset (square s.plaq.val.1 s.plaq.val.2)

lemma turn_peak (s : Slot) (U : X) : HasDerivAt (fun θ => s.eval (lit U θ)) (CurlOn s U) 0 := by
  let t (θ : ℝ) := travel (lit U θ) 0 s.walk
  let Y (θ : ℝ) := faceValue (lit U θ) (s.offset, s.plaq)
  let P θ := t θ * Y θ * (t θ)⁻¹
  let b := G.colorMat (Exterior.linkSum U 0 s.walk)
  let a := G.colorMat (CurlOn s U)
  have hu : lit U 0 = 1 := by
    ext1 i
    simp [lit]
  have hz : t 0 = 1 := by
    unfold t
    rw [hu]
    exact Pressure.one _
  have hi : Y 0 = 1 := by
    unfold Y
    rw [hu]
    exact Pressure.one _
  have hd : HasDerivAt (fun θ => G.mat (t θ)) b 0 := priced s.walk U 0
  have hb : HasDerivAt (fun θ => G.mat (Y θ)) a 0 := priced ..
  have hP : HasDerivAt (fun θ => G.mat (P θ)) a 0 := by
    simp only [P, G.mat_mul, G.mat_inv]
    apply ((hd.mul hb).mul hd.star).congr_deriv
    simp only [hz, hi, G.mat_one, star_one, Pi.mul_apply, one_mul, mul_one,
      show star b = -b from G.colorMat_skew _]
    abel
  have he : HasDerivAt (fun θ => (1 / 2 : ℝ) • (G.mat (P θ) - star (G.mat (P θ)))) a 0 := by
    apply ((hP.sub hP.star).const_smul (1 / 2 : ℝ)).congr_deriv
    rw [show star a = -a from G.colorMat_skew _, sub_neg_eq_add, ← two_smul ℝ, smul_smul,
      div_mul_cancel₀ _ (two_ne_zero' ℝ), one_smul]
  rw [show
      (fun θ => s.eval (lit U θ)) =
        G.projectColor ∘ (fun θ => (1 / 2 : ℝ) • (G.mat (P θ) - star (G.mat (P θ))))
      from
      funext fun θ => by
        rw [Slot.eval, ← G.curvature_conjugate]
        unfold Function.comp
        dsimp only [Gauge.curvature]
        rw [G.mat_inv]]
  exact
    (G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt _ he).congr_deriv
      (G.project_colorMat _)

def probeSlots : X →ₗ[ℝ] GaugePanel G A.size
    where
  toFun x i := CurlOn (A.looks i) x
  map_add' := fun a b => by
    funext i
    change CurlOn _ (a + b) = CurlOn _ a + CurlOn _ b
    simp_rw [CurlOn, G03.square_sum, Pi.add_apply]
    abel
  map_smul' := fun a b => by
    funext i
    change CurlOn _ (a • b) = a • CurlOn _ b
    simp [CurlOn, G03.square_sum, smul_sub, smul_add]

def evaluateL (i : Labels.Key G) : Module.Dual ℝ X :=
  (Survey.component i).comp (A.extract.toLinearMap ∘ₗ probeSlots A)

lemma proportional (x : X) : HasDerivAt (fun t => Bid.mapped A.looks (lit x t)) (probeSlots A x) 0 :=
  hasDerivAt_pi.mpr (fun i => turn_peak (A.looks i) x)

lemma panelD (x : X) : HasDerivAt (fun t => A.reading (lit x t)) (A.extract (probeSlots A x)) 0 := by
  have hp := proportional A x
  let f θ := Bid.mapped A.looks (lit x θ)
  have he : f 0 = 0 := by
    have hv : lit x 0 = 1 := by
      ext1 i
      simp [lit]
    unfold f Bid.mapped
    rw [hv]
    ext1 i
    unfold Slot.eval
    simp_rw [show faceValue (1 : CoverConfig G) _ = 1 from Pressure.one _, G.curvature_unit, map_zero]
    rfl
  have hd : HasFDerivAt A.recover A.extract (f 0) := by
    rw [he]
    exact (A.recover_smooth.differentiable (by simp) _).hasFDerivAt
  exact hd.comp_hasDerivAt 0 hp

lemma sales (i : Labels.Key G) (x : X) :
    HasDerivAt (fun t => (reader A (MvPolynomial.X i) (lit x t)).re) (evaluateL A i x) 0 := by
  rw [show (fun t => (reader A (MvPolynomial.X i) (lit x t)).re) = _ from ?_]
  exact
    (LinearMap.toContinuousLinearMap (Survey.component i)).hasFDerivAt.comp_hasDerivAt (f := fun t =>
      A.reading (lit x t)) _ (panelD A x)
  ext1 t
  unfold reader
  rw [Labels.read, MvPolynomial.aeval_X]
  rfl
local notation "W" => Lot G (Wire A)

lemma exposes (i : Labels.Key G) (x : X) :
    layer (x ∘ site A) (fun z : W => (reader A (MvPolynomial.X i) (packetU A z)).re) 0 =
      evaluateL A i x := by
  let F (z : W) := (reader A (MvPolynomial.X i) (packetU A z)).re
  have hp (t : ℝ) : (reader A (MvPolynomial.X i) (lit x t)).re = F (t • ((x ∘ site A) : W)) := by
    rw [photographed A]
    rfl
  have he := sales A i x
  rw [funext hp] at he
  let V : W := x ∘ site A
  have ht : HasDerivAt (fun t : ℝ => t • V) V (0 : ℝ) := by
    simpa only [one_smul] using! (hasDerivAt_id' (0 : ℝ)).smul_const V
  obtain hx := ((calm_R A (MvPolynomial.X i)).differentiableAt (by simp)).hasFDerivAt
  exact (hx.comp_hasDerivAt_of_eq 0 ht (by rw [zero_smul])).unique he
end YM.WilsonMS.Webs
