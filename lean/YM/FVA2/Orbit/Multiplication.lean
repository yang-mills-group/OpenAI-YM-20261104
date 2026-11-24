import YM.FVA2.Orbit.Geometry
/-!
# Haar density calculus in the origin germ

Keep jacobians relative to both componentwise log multiplication sides.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
open Function Set Filter Finset Topology LocalH Next.SectorChange
open scoped ContDiff Topology MeasureTheory Matrix.Norms.Frobenius Classical BigOperators
variable {G:Gauge}
local notation "C" => G.Color

section shift
variable {E F K: Type*} [TopologicalSpace E][TopologicalSpace F][Zero E][Zero F]
lemma aimed {f:E→F} (h:ContinuousAt f 0) (k:f 0=0) : Tendsto f (𝓝 0) (𝓝 0):= k ▸ (h.tendsto)
variable {L:Filter K}
lemma tup {f:K→E}{g:K→F}(h:Tendsto f L (𝓝 0))(k:Tendsto g L (𝓝 0)): Tendsto (fun x=>(f x,g x)) L (𝓝 0):= h.prodMk_nhds k
lemma eq_from_exp {f g: K→C} (h : Tendsto f L (𝓝 0)) (k : Tendsto g L (𝓝 0)) (hh: ∀ᶠ x in L, G.lieExp (f x)=G.lieExp (g x)) : f=ᶠ[L] g:= by
    filter_upwards [h.eventually G.plog_left,k.eventually G.plog_left,hh] with x hx hy hz
    exact hx.symm.trans ((congr_arg (LocalH.snap G) hz).trans hy)
end shift

local notation "e" => G.lieExp
def merge (p q:C) := LocalH.snap G (G.lieExp p * G.lieExp q)
@[simp] lemma merge_zero : merge (0:C) 0=0 := by unfold merge LocalH.snap; simp
lemma merge_germ : ContDiffAt ℝ ω (uncurry (merge (G:=G))) (0:C × C):= by
    let z : C×C→G.Mat := fun x => G.mat (e x.1)*G.mat (e x.2)
    have he : ContDiff ℝ ω z := (G.exp_jet.comp contDiff_fst).mul (G.exp_jet.comp contDiff_snd)
    have hz : z 0=1:= by simp [z]
    exact (hz.symm ▸ G.plog_diff : ContDiffAt ℝ ω G.plog (z 0)).comp (f:=z) 0 he.contDiffAt
lemma merged : ∀ᶠ x : C×C in 𝓝 0,e (merge x.1 x.2) = e x.1 * e x.2 := by
    let f (x:C×C):= e x.1 * e x.2; have hz:f 0=1:= by simp [f]
    exact (hz ▸ ((G.lieExp_cont.comp continuous_fst).mul (G.lieExp_cont.comp continuous_snd)|>.tendsto 0) : Tendsto f (𝓝 0) (𝓝 1)).eventually G.plog_right
lemma merge_left : ∀ᶠ x in 𝓝 (0:C), merge (0:C) x=x := by
    filter_upwards [G.plog_left] with x hx; unfold merge; simp only [G.mat_lieExp_zero,one_mul]; exact hx
lemma merge_right : ∀ᶠ x in 𝓝 (0:C), merge x (0:C)=x:= by
    filter_upwards [G.plog_left] with x hx; unfold merge; simp only [G.mat_lieExp_zero,mul_one]; exact hx
lemma merge_flip : ∀ᶠ x:C×C in 𝓝 0, merge x.1 x.2= -(merge (-x.2) (-x.1)):= by
    let v (p:C×C) : C×C := -p.swap; have hv : Tendsto v (𝓝 0) (𝓝 0) := aimed (by unfold v; fun_prop) (by simp [v])
    let m : C×C→C:= uncurry merge; have h : Tendsto m (𝓝 0) (𝓝 0) := aimed merge_germ.continuousAt merge_zero; let k := fun t:C=>-t; have hk : Tendsto k (𝓝 0) (𝓝 0):= aimed (by unfold k; fun_prop) neg_zero
    apply eq_from_exp h (hk.comp (h.comp hv))
    filter_upwards [merged (G:=G),hv.eventually merged] with x hx hy
    change e _= e (-(merge (v x).1 (v x).2))
    rw [ show m x=merge x.1 x.2 from rfl, hx,exp_negative,hy,mul_inv_rev]
    change _= (e (-x.1))⁻¹*(e (-x.2))⁻¹; simp [exp_negative]
lemma spin_pos : ∀ᶠ x in 𝓝 (0:C), 0 < spin G x := MS.Bare.Maurer.lives G
lemma spin_even : ∀ᶠ x in 𝓝 (0:C), spin G (-x)=spin G x:= by
    have h : Tendsto (fun x:C=>-x) (𝓝 0) (𝓝 0):= aimed continuous_neg.continuousAt neg_zero
    filter_upwards [MS.Bare.Maurer.opposite (G:=G),h.eventually spin_pos,spin_pos] with x hx hy hz
    exact Real.log_injOn_pos hy hz hx
lemma merge_diff : ∀ᶠ x:C×C in 𝓝 0, DifferentiableAt ℝ (merge x.1) x.2 ∧ DifferentiableAt ℝ (fun u=>merge u x.2) x.1:= by
    filter_upwards [(merge_germ (G:=G)).eventually (by simp)] with x hx
    exact ⟨ (hx.differentiableAt (by simp)).comp (f:=fun a : C=>(x.1,a)) x.2 (differentiableAt_const _|>.prodMk differentiableAt_id),
      (hx.differentiableAt (by simp)).comp (f:=fun a : C=>(a,x.2)) x.1 (differentiableAt_id.prodMk (differentiableAt_const _))⟩
-- left multiplication
lemma price_left : ∀ᶠ x:C×C in 𝓝 0, spin G (merge x.1 x.2) * (fderiv ℝ (merge x.1) x.2).det = spin G x.2 := by
    let f (x:C×C):= e x.1 * e x.2; have hz:f 0=1:= by simp [f]
    have hv : Continuous f:= (G.lieExp_cont.comp continuous_fst).mul (G.lieExp_cont.comp continuous_snd)
    obtain ⟨r,hr,H⟩:= geom_patch G; let S:= e '' Metric.ball 0 r; have h:=H r (le_refl r); have hu:(1:G.El) ∈ S:=⟨0,Metric.mem_ball_self hr,G.mat_lieExp_zero⟩
    exact ((hz ▸ hv.tendsto 0 : Tendsto f (𝓝 0) (𝓝 1)).eventually (h.1.mem_nhds hu)).mono (fun x hx=> spins G h hu (u:=e x.1) x.2 hx)
lemma det_cost_right {x : C×C} (h: ∀ᶠ y:C×C in 𝓝 x, merge y.1 y.2= -(merge (-y.2) (-y.1))) (hh: DifferentiableAt ℝ (merge (-x.2)) (-x.1)): (fderiv ℝ (fun u=>merge u x.2) x.1).det=(fderiv ℝ (merge (-x.2)) (-x.1)).det:= by
    let T : C≃ₗ[ℝ]C:=LinearEquiv.neg ℝ; let t:=T.toContinuousLinearEquiv.toContinuousLinearMap; let p:=merge (-x.2); let v:= fderiv ℝ p (t x.1); let k:= (t ∘L v) ∘L t
    have he : HasFDerivAt (fun u=>merge u x.2) k x.1 := by
      apply ((t.hasFDerivAt.comp (t x.1) (hh.hasFDerivAt : HasFDerivAt p v (t x.1))).comp x.1 t.hasFDerivAt).congr_of_eventuallyEq
      exact ((continuous_id.prodMk (f:=id) (continuous_const (y:=x.2))).tendsto x.1).eventually h
    have hv := LinearMap.det_conj v.toLinearMap T
    rw [he.fderiv]
    exact hv
lemma price_right : ∀ᶠ x:C×C in 𝓝 0, spin G (merge x.1 x.2)*(fderiv ℝ (fun u=>merge u x.2) x.1).det= spin G x.1:= by
    let f (p:C×C) : C×C:= -p.swap; have h : Tendsto f (𝓝 0) (𝓝 0):= aimed (by unfold f; fun_prop) (by simp [f]); have hx:= (aimed (merge_germ (G:=G)).continuousAt merge_zero).comp h
    filter_upwards [(merge_flip (G:=G)).eventually_nhds, h.eventually (price_left.and merge_diff),hx.eventually spin_even,(continuous_fst.tendsto (0:C×C)).eventually spin_even] with x hp hv he hn
    rw [ hp.self_of_nhds, show spin G (-(merge (-x.2) (-x.1)))=spin G (merge (-x.2) (-x.1)) from he, det_cost_right hp hv.2.1, show spin G (merge (-x.2) (-x.1)) *(fderiv ℝ (merge (-x.2)) (-x.1)).det=spin G (-x.1) from hv.1, hn]
end YM.FVA2.Orbit
