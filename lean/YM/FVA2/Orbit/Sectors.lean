import YM.FVA2.Orbit.Unroot
import YM.FVA2.Slice.Reduction
/-!
# The particular Landau weight calculated in MS's Wick predicate
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice.FiniteOrbit
open Function Set Filter Finset Topology Lattice MeasureTheory
open Pert Orb
open Orbit
open MS MS.Koszul MS.Native MS.Bare MS.Native.Chart
open LocalH
open scoped ContDiff Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators Matrix
variable {G:Gauge} {n:Side}
local notation "T" => Site n
local notation "I" => PertExtension.Orb.OEdge n
local notation "Z" => Parameter G n
local notation "Y" => Potential G n
local notation "R" => Root G n
local notation "V" => Rep G n
local notation "S" => SiteGhost G n
local notation "L" => Transverse G n
local notation "C" => G.Color
local notation "F" => Edge T
local notation "e" => G.lieExp
local notation "θ" => R×L
open scoped Classical
section haar
open PertExtension PertExtension.Orb
lemma doubling (ev: Even n.val)(f:F→ℝ)(h:∀ i,f (reflect i)=f i) : ∑ i, f i= ∑ i:I, f i.val * 2 := by
    let p:=fun x:F=>eR x=x
    let R':I≃ {x:F // ¬ p x}:=
      ⟨fun i=>⟨reflect i.val,by unfold p; rw [eR_reflect,i.property]; exact Ne.symm (no_fixed_edge ev _)⟩,
       fun j=>⟨reflect j.val, (eR_reflect _).trans ((eR_spec _).resolve_left j.property)⟩,
       fun i=>Subtype.ext (reflect_reflect _), fun j=>Subtype.ext (reflect_reflect _)⟩
    let f':=fun i:I=> f i.val; have ht: ∑ i:I,f' i=∑ j:{x:F //¬ p x}, f j.val:= Fintype.sum_equiv R' _ _ (fun i=> (h i.val).symm)
    -- Fintype I definition likely defeq
    rw [← Fintype.sum_subtype_add_sum_subtype p,← ht]; change (∑ i:I,f' i)+_=_; rw [← sum_mul]; ring
lemma hairs (ev:Even n.val): ∀ᶠ x:L in 𝓝 0,hair (traceLink G n x)=Real.exp (Slice.haar G n x):= by
    let Z':=incCL G n; have hz : Tendsto Z' (𝓝 0) (𝓝 0):= aimed (show ContinuousAt (Z':L→Chart.City G T) 0 from Z'.cont.continuousAt) Z'.map_zero
    filter_upwards [hz.eventually ( eventuallY (G:=G) (n:=n) ) ] with x hx
    let f (i:F):= Maurer.lac (includeA G n x i); have h(i:F) : f (reflect i)=f i:= by unfold f; rw [show includeA G n x (reflect i) = - includeA G n x i from reflect_at x.val i]; exact (hx i).2
    have h': Slice.haar G n x=∑ i:I, f i.val:= by unfold Slice.haar; rw [totalH]; change (∑ i,f i)/2=_; rw [doubling ev f h, ← sum_mul];ring
    rw [h', Real.exp_sum]; exact Finset.prod_congr rfl fun i _=> (Real.exp_log (hx i.val).1).symm
 where
    eventuallY {G:Gauge}{n:Side} : ∀ᶠ x : Chart.City G (Site n) in 𝓝 0,∀ i:Edge (Site n), 0<spin G (x i) ∧ Maurer.lac (-x i)=Maurer.lac (x i):= eventually_all.mpr fun i : Edge (Site n)=> (continuous_apply i|>.tendsto (0:Chart.City G (Site n))).eventually (spin_pos.and Maurer.opposite)
end haar
variable {A J:Type} [Fintype J][DecidableEq J]
def broad (a:Axes G n A J) : Module.Basis J ℝ R:= a.c.map (renorm G n)
variable (a:Axes G n A J) (ev:Even n.val)
local notation "b" => broad a
local notation "N" => land G ev
private lemma fd : ∀ᶠ x:L in 𝓝 0, ∀ z y, fderiv ℝ (N).tilt (0,x) (z,y)=vertical (traceLink G n x) z+traceLink G n y:= by
 let σ:= traceCont G n; filter_upwards [axes_later (⇑σ) (germ_trace G n) σ.map_zero] with x h
 rw [show fderiv ℝ σ x=σ from ContinuousLinearMap.fderiv (E:=Transverse G n) («F»:=Rep G n) (𝕜:=ℝ) σ] at h; exact h
private lemma coords (j:J) : (b).coord j= root_test ev (a.Y j) ∘ₗ vertical (0:V):= (b).ext (fun i=>by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self,Finsupp.single_apply,LinearMap.comp_apply, show broad a i=_ from Module.Basis.map_apply a.c (renorm G n) i]; have he:= (unrooted (G:=G) ev).self_of_nhds (a.Y j) (a.c i)
    simp_rw [map_zero] at he; simp only [←he,a.flat_pair,eq_comm] )
section screenCoordinates
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
private def screenDerivative (s : Screen G n E) (x : E) : R × E →L[ℝ] R × E :=
  s.hurdle.symm.toContinuousLinearMap ∘L fderiv ℝ s.tilt (0,x)
private def screenRoot (s : Screen G n E) (x : E) : R →L[ℝ] R :=
  ContinuousLinearMap.fst ℝ R E ∘L screenDerivative s x ∘L ContinuousLinearMap.inl ℝ R E
end screenCoordinates
private abbrev orbitDifferential (ev : Even n.val) (x : L) : θ →L[ℝ] θ :=
  screenDerivative (G:=G) (n:=n) (E:=L) (land G ev) x
private abbrev rootDifferential (ev : Even n.val) (x : L) : R →L[ℝ] R :=
  screenRoot (G:=G) (n:=n) (E:=L) (land G ev) x

private def derivativeAt (ev : Even n.val) (x : L) : Prop :=
  ∀ z y, fderiv ℝ (land G ev).tilt (0,x) (z,y) =
    vertical (traceLink G n x) z + traceLink G n y

private lemma horizontal_fixed (x : L) (h : derivativeAt ev x) (y : L) :
    orbitDifferential ev x (0,y) = (0,y) := by
  apply (land G ev).hurdle.injective
  change (land G ev).hurdle ((land G ev).hurdle.symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  calc _ = vertical (traceLink G n x) (0:R) + traceLink G n y := h 0 y
       _ = vertical 0 (0:R) + traceLink G n y := by simp only [map_zero]
       _ = _ := (tilted_here ev 0 y).symm

private lemma vertical_split (x : L) (h : derivativeAt ev x) (z : R) :
    vertical (traceLink G n x) z = vertical 0 (rootDifferential ev x z) +
      traceLink G n (orbitDifferential ev x (z,0)).2 := by
  let u := orbitDifferential ev x (z,0)
  change _ = vertical 0 u.1 + traceLink G n u.2
  rw [← tilted_here ev u.1 u.2]
  change _ = (land G ev).hurdle ((land G ev).hurdle.symm _)
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact ((h z 0).trans (by rw [map_zero,add_zero])).symm

private lemma root_matrix (x : L) (h : derivativeAt ev x)
    (hz : ∀ p q : S, pair x p q = root_test ev p (vertical (traceLink G n x) (renorm G n q))) :
    LinearMap.toMatrix b b (rootDifferential ev x).toLinearMap = a.M x := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (b).coord i (rootDifferential ev x (b j)) = pair x (a.Y i) (a.c j)
  rw [coords a ev, LinearMap.comp_apply, hz, ← show broad a j = _ from
    Module.Basis.map_apply a.c (renorm G n) j, vertical_split ev x h, map_add,
    show root_test ev _ (traceLink G n _) = 0 from tests_blank ev (a.Y i) _, add_zero]

private lemma block_determinant {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (M : E₁ × E₂ →L[ℝ] E₁ × E₂) (Q : E₁ →L[ℝ] E₁)
    (h : ∀ y : E₂, M (0,y) = (0,y)) (hq : ∀ z : E₁, (M (z,0)).1 = Q z) :
    ContinuousLinearMap.det (M:=E₁ × E₂) («R»:=ℝ) M = ContinuousLinearMap.det (M:=E₁) («R»:=ℝ) Q := by
  let swapAxes : (E₂ × E₁) ≃L[ℝ] (E₁ × E₂) := ContinuousLinearEquiv.prodComm ℝ E₂ E₁
  let U := (swapAxes.symm.toContinuousLinearMap ∘L M) ∘L swapAxes.toContinuousLinearMap
  have conjugate : ContinuousLinearMap.det (M:=E₂ × E₁) («R»:=ℝ) U = ContinuousLinearMap.det (M:=E₁ × E₂) («R»:=ℝ) M :=
    LinearMap.det_conj (M:=E₁ × E₂) («N»:=E₂ × E₁) M.toLinearMap swapAxes.symm.toLinearEquiv
  have fixed (y : E₂) : U (y,0) = (ContinuousLinearMap.id ℝ E₂ y,0) := by
    change (M (0,y)).swap = (y,0)
    exact congrArg Prod.swap (h y)
  have root (z : E₁) : (U (0,z)).2 = Q z := hq z
  rw [←conjugate, upper U (ContinuousLinearMap.id ℝ E₂) Q fixed root,
    show ContinuousLinearMap.det (M:=E₂) («R»:=ℝ) (ContinuousLinearMap.id ℝ E₂) = 1 from map_one LinearMap.det, one_mul]

private lemma screen_jacobian {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Screen G n E) (x : E) (h : ∀ y : E, screenDerivative s x (0,y) = (0,y)) :
    s.relative (0,x) = ContinuousLinearMap.det (M:=Root G n) («R»:=ℝ) (screenRoot s x) := by
  exact (adjust (E:=Root G n × E) («F»:=Rep G n) s.hurdle (fderiv ℝ s.tilt (0,x))).trans
    (block_determinant (E₁:=Root G n) (E₂:=E) (screenDerivative s x) (screenRoot s x) h (fun _ => rfl))

private lemma measured_determinant (x : L) (h : derivativeAt ev x)
    (hz : ∀ p q : S, pair x p q = root_test ev p (vertical (traceLink G n x) (renorm G n q))) :
    ContinuousLinearMap.det (M:=Root G n) («R»:=ℝ) (rootDifferential (G:=G) (n:=n) ev x) = (a.M x).det :=
  (LinearMap.det_toMatrix b (rootDifferential (G:=G) (n:=n) ev x).toLinearMap).symm.trans
    (congrArg Matrix.det (root_matrix (G:=G) (n:=n) a ev x h hz))

set_option maxHeartbeats 200000 in
lemma jac_FP : ∀ᶠ x:L in 𝓝 0,(N).relative (0,x)= (a.M x).det:= by
  filter_upwards [fd (G:=G) ev,unrooted (G:=G) ev] with x h hz
  exact (screen_jacobian (G:=G) (n:=n) (E:=L) (land G ev) x (horizontal_fixed (G:=G) (n:=n) ev x h)).trans
    (measured_determinant (G:=G) (n:=n) a ev x h hz)
/-- No determinant set to one by hand: the Hessian-independent relative FP use matches at MS master.
Local equality only; no statements about FP positivity away from the germ. -/
theorem sectors : (N).weight =ᶠ[𝓝 0] fun x=> Real.exp (Slice.haar G n x) * (a.M x).det:= by
 filter_upwards [hairs (G:=G) ev, jac_FP a ev] with x hx hv
 change hair (traceLink G n x) * _=_; rw [hx,hv]
end YM.FVA2.Slice.FiniteOrbit
