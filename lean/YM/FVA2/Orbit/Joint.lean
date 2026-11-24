import YM.FVA2.Orbit.Multiplication
/-!
# Components at vertices or representative edges
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
open Function Set Filter Finset Topology LocalH Next.SectorChange
open scoped ContDiff Topology MeasureTheory Matrix.Norms.Frobenius Classical BigOperators
variable {G:Gauge} {I:Type} [Fintype I]
local notation "E" => I→G.Color
local notation "e" => G.lieExp
-- treat `V=Root`, `Rep` uniformly, reduce angle to two shift+merge
/-- Product Haar link or gauge-angle germ with dimension scalar omitted. -/
def hair (p:I→G.Color) := ∏ i, LocalH.spin G (p i)
lemma hair_analytic : ContDiff ℝ ω (hair (I:=I) (G:=G)):= by
    unfold hair; rw [contDiff_iff_contDiffAt]; intro x; exact contDiffAt_prod (fun i _ => (LocalH.spin_deriv G (x i)).comp (f:=fun x:E => x i) x (contDiff_apply .. |>.contDiffAt) )
@[simp] lemma hair0 : hair (0:E)=1:= by simp [hair,LocalH.spin_zero]

/-- Group law of the germ of rooted site gauges (or of all links in representative orientation). -/
def circle (p q:I→G.Color) : I→G.Color:= fun i=> merge (p i) (q i)
omit [Fintype I] in
@[simp] theorem circle0 : circle (0:E) (0:E)=0:= funext (fun _=> merge_zero)
omit [Fintype I] in
lemma slogan (i:I) : Tendsto (fun p:(E)× (E)=>(p.1 i,p.2 i)) (𝓝 0) (𝓝 0) := aimed (by fun_prop) rfl
lemma join_germ : ContDiffAt ℝ ω (uncurry (circle (I:=I) (G:=G))) (0: (E) × (E)):= by
    refine contDiffAt_pi.mpr fun i=> ?_
    let p:= fun x:(E)× (E) => (x.1 i,x.2 i)
    exact merge_germ.comp (f:=p) (x:=(0:(E) × (E))) (by unfold p; fun_prop)
omit [Fintype I] in
lemma joins_zero (p:E) : p=0 ↔ ∀ i, p i=0:= ⟨fun h i=> by rw [h]; rfl, fun h=>funext h⟩
lemma left_turn : ∀ᶠ p : (E) in 𝓝 0, circle 0 p = p:= ((eventually_all.mpr (fun i:I=> (continuous_apply i|>.tendsto (0:E)).eventually (merge_left (G:=G))))).mono (fun _ hx=> funext hx)
lemma right_turn : ∀ᶠ p : (E) in 𝓝 0, circle p 0 = p:= ((eventually_all.mpr (fun i:I=> (continuous_apply i|>.tendsto (0:E)).eventually (merge_right (G:=G))))).mono (fun _ hx=> funext hx)
lemma sparked : ∀ᶠ p : (E) × (E) in 𝓝 0,∀ i, e (circle p.1 p.2 i)= e (p.1 i)*e (p.2 i):= eventually_all.mpr (fun i : I=> (slogan (G:=G) i).eventually merged)
lemma diff_circle : ∀ᶠ p : (E)×(E) in 𝓝 0,DifferentiableAt ℝ (circle p.1) p.2 ∧ DifferentiableAt ℝ (fun a=>circle a p.2) p.1:= by
    filter_upwards [(join_germ (I:=I) (G:=G)).eventually (by simp)] with x hx
    have h:= hx.differentiableAt (by simp)
    exact ⟨h.comp (f:=fun p : (E)=>(x.1,p)) x.2 (differentiableAt_const _|>.prodMk differentiableAt_id),h.comp (f:=fun p : (E)=>(p,x.2)) x.1 (differentiableAt_id.prodMk (differentiableAt_const _))⟩
lemma pi_det {C:Type*} [NormedAddCommGroup C][NormedSpace ℝ C][FiniteDimensional ℝ C] (f:I→C→C)(v:I→C) (h:∀ i, DifferentiableAt ℝ (f i) (v i)): (fderiv ℝ (fun w:I→C=> fun i=> f i (w i)) v).det=∏ i,(fderiv ℝ (f i) (v i)).det:= by
    let F i:=fderiv ℝ (f i) (v i); let D := ContinuousLinearMap.pi fun i=> F i ∘L ContinuousLinearMap.proj i
    have hpi (i:I): HasFDerivAt (fun x:I→C=> x i) (ContinuousLinearMap.proj i : (I→C)→L[ℝ]C) v := (ContinuousLinearMap.proj i : (I→C)→L[ℝ]C).hasFDerivAt
    rw [show fderiv ℝ (fun w:I→C=> fun i=> f i (w i)) v=D from (hasFDerivAt_pi.mpr (fun i:I => (h i).hasFDerivAt.comp (f:=fun p : I→C=>p i) v (hpi i))).fderiv]; exact LinearMap.det_pi (fun i=>(F i).toLinearMap)
lemma joins_left : ∀ᶠ p : (E)×(E) in 𝓝 0,hair (circle p.1 p.2) * (fderiv ℝ (circle p.1) p.2).det=hair p.2:= by
    filter_upwards [eventually_all.mpr (fun i:I=> (slogan (G:=G) i).eventually (merge_diff.and price_left))] with p h
    rw [show (fderiv ℝ (circle p.1) p.2).det = _ from pi_det (fun i : I=> merge (p.1 i)) p.2 (fun i=>(h i).1.1), hair,hair, ← prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => (h i).2)
lemma joins_right : ∀ᶠ p : (E)×(E) in 𝓝 0,hair (circle p.1 p.2) * (fderiv ℝ (fun a=>circle a p.2) p.1).det=hair p.1:= by
    filter_upwards [eventually_all.mpr (fun i:I=> (slogan (G:=G) i).eventually (merge_diff.and price_right))] with p h
    rw [show (fderiv ℝ (fun a=>circle a p.2) p.1).det = _ from pi_det (fun i : I=> fun q=> merge q (p.2 i)) p.1 (fun i=>(h i).1.2), hair,hair, ← prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => (h i).2)
lemma gate_left : ∀ᶠ p : (E) in 𝓝 0,hair p * (fderiv ℝ (circle p) 0).det=1:= by
    filter_upwards [ (continuous_id.prodMk (continuous_const (y:=(0:E)))|>.tendsto (0:E)).eventually joins_left, right_turn (G:=G) (I:=I)] with p h ht
    nth_rw 1 [← ht]; exact h.trans hair0
lemma gate_right : ∀ᶠ p : (E) in 𝓝 0,hair p * (fderiv ℝ (fun a=>circle a p) 0).det=1:= by
    filter_upwards [ ((continuous_const (y:=(0:E))).prodMk continuous_id |>.tendsto (0:E)).eventually joins_right, left_turn (G:=G) (I:=I)] with p h ht
    nth_rw 1 [← ht]; exact h.trans hair0
end YM.FVA2.Orbit
