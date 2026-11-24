import YM.FVA2.Orbit.Joint
/-!
# Rooted gauge action on quotient links
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
open Function Set Filter Finset Topology PertExtension PertExtension.Orb LocalH Next.SectorChange Lattice Wilson
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical BigOperators
variable {G:Gauge} {n:Side}
local notation "T" => Site n
local notation "R" => Root G n
local notation "V" => Rep G n
local notation "I" => OEdge n
local notation "e" => G.lieExp
private def head : R →ₗ[ℝ] V:= LinearMap.pi fun i : I=> atSite i.val.1
private def tail : R →ₗ[ℝ] V:= LinearMap.pi fun i : I=> atSite (i.val.1 + step i.val.2)
private lemma head_t : Tendsto ⇑(head (G:=G) (n:=n)) (𝓝 0) (𝓝 0):= aimed (head.continuous_of_finiteDimensional.continuousAt) head.map_zero
private lemma tail_t : Tendsto ⇑(tail (G:=G) (n:=n)) (𝓝 0) (𝓝 0):= aimed (tail.continuous_of_finiteDimensional.continuousAt) tail.map_zero

def angle (z:R)(p:V) := circle (circle (-(head z)) p) (tail z)
@[simp] lemma angle0 : angle (0:R) (0:V)=0:= by simp [angle]
lemma angle_germ : ContDiffAt ℝ ω (uncurry (angle (G:=G) (n:=n))) 0:= by
    let v:=circle («I»:=I) (G:=G); let t := fun p:R×V => (-(head p.1),p.2); have ht:t (0:R×V)=0:= by simp [t]
    have h : ContDiffAt ℝ ω (uncurry v) 0:= join_germ
    have hm : ContDiffAt ℝ ω (uncurry v ∘ t) 0:= (ht.symm ▸ h : ContDiffAt ℝ ω (uncurry v) (t 0)).comp (0:R×V) (((head (G:=G) (n:=n)).toContinuousLinearMap.contDiff.comp contDiff_fst).contDiffAt.neg.prodMk contDiffAt_snd)
    let y:= fun p:R×V => ((uncurry v ∘ t) p,tail p.1); have hy:y 0=0:= by unfold y; rw [comp_apply,ht,show uncurry v 0=0 from circle0,Prod.fst_zero,map_zero]; rfl
    exact (hy.symm ▸ h : ContDiffAt ℝ ω (uncurry v) (y 0)).comp (f:=y) 0 (hm.prodMk (((tail (G:=G) (n:=n)).toContinuousLinearMap.contDiff.comp contDiff_fst).contDiffAt))
lemma angle_id : ∀ᶠ p:V in 𝓝 0, angle (0:R) p=p:= by
    filter_upwards [left_turn («I»:=I) (G:=G),right_turn («I»:=I) (G:=G)] with p hx hy; unfold angle; rw [map_zero,map_zero,neg_zero,hx,hy]
-- exact Jacobian for each orbit
lemma angle_wind : ∀ᶠ z:R × V in 𝓝 0, (hair (angle z.1 z.2)*(fderiv ℝ (angle z.1) z.2).det=hair z.2) ∧ DifferentiableAt ℝ (angle z.1) z.2:= by
    let c:=circle («I»:=I) (G:=G); let l (p:R×V):= (-(head p.1),p.2); let r (p:R×V):= (uncurry c (l p),tail p.1)
    have hF := continuous_fst.tendsto (0:R×V); have hl : Tendsto l (𝓝 0) (𝓝 0):= tup ( (aimed (continuous_neg.continuousAt) ((show -(0:V)=0 from neg_zero))).comp (head_t.comp hF)) (continuous_snd.tendsto (0:R×V))
    have hr : Tendsto r (𝓝 0) (𝓝 0):= tup ((aimed join_germ.continuousAt circle0).comp hl) (tail_t.comp hF)
    filter_upwards [hl.eventually (joins_left.and diff_circle),hr.eventually (joins_right.and diff_circle)] with p ha hb
    let f:= c (l p).1; let g:=fun q=>c q (r p).2; let y:=p.2; let v:=f y; have h:DifferentiableAt ℝ f y:=ha.2.1; have k:DifferentiableAt ℝ g (f y):=hb.2.2
    refine ⟨?_,k.comp y h⟩
    change hair (g v) * (fderiv ℝ (g ∘ f) y).det=hair y
    rw [fderiv_comp y k h, show (fderiv ℝ g _ ∘L fderiv ℝ f y).det=_ from LinearMap.det_comp ..]
    rw [←mul_assoc, show hair (g v) * LinearMap.det (fderiv ℝ g (f y)).toLinearMap=hair v from hb.1]; exact ha.1

def gang (p:R)(x:T) := (e (atSite x p))⁻¹
lemma gang_neg (p:R)(x:T) : gang p (-x)=gang p x:= by rw [gang,site_neg]; rfl
@[simp] lemma gang_zero (p:R) : gang p 0=1:= by simp [gang]
def play (z:R)(p:V) := gauge (gang z) (ignite p)
private lemma price (p:V)(i:I) : ignite p i.val=e (p i):= lift_at _ i
lemma physical : ∀ᶠ x:R×V in 𝓝 0, ignite (angle x.1 x.2)= play x.1 x.2:= by
    let c:=circle («I»:=I) (G:=G); let l (p:R×V):= (-(head p.1),p.2); let r (p:R×V):= (uncurry c (l p),tail p.1)
    have hF := continuous_fst.tendsto (0:R×V); have hl : Tendsto l (𝓝 0) (𝓝 0):= tup ( (aimed (continuous_neg.continuousAt) ((show -(0:V)=0 from neg_zero))).comp (head_t.comp hF)) (continuous_snd.tendsto (0:R×V))
    have hr : Tendsto r (𝓝 0) (𝓝 0):= tup ((aimed join_germ.continuousAt circle0).comp hl) (tail_t.comp hF)
    filter_upwards [hl.eventually sparked,hr.eventually sparked] with p ha hb
    let f := fun i : I=>e (angle p.1 p.2 i)
    let k := fun i:I=> play p.1 p.2 i.val; have hk:k=f:= by
      funext i; rw [show f i=e (circle (r p).1 (r p).2 i) from rfl,hb,show (r p).1=circle (l p).1 (l p).2 from rfl,ha]; unfold k play; rw [Lattice.gauge, price]; unfold gang; rw [inv_inv]; rw [show (l p).1 i = -(atSite i.val.1 p.1) from rfl, exp_negative];rfl
    exact funext fun x=> by rw [show ignite (angle p.1 p.2)=liftLinks f from rfl,← hk]; exact (path_law (gang p.1) _ (gang_neg _) x).symm

lemma mix_gang : ∀ᶠ z:R×R in 𝓝 0,∀ i:T, gang (circle z.1 z.2) i= gang z.2 i * gang z.1 i:= by
    filter_upwards [sparked («I»:=Away n) (G:=G)] with z hz
    intro i; unfold gang; unfold atSite; split
    next h=> simp only [LinearMap.proj_apply,hz,mul_inv_rev]
    · simp

section
lemma born {K:Type*} {L:Filter K} {f g:K→Rep G n} (h : Tendsto f L (𝓝 0)) (k : Tendsto g L (𝓝 0)) (hh: ∀ᶠ x in L, ignite (f x)=ignite (g x)) : f=ᶠ[L] g:= by
  have e' (i:I) : ∀ᶠ x in L, f x i=g x i:= eq_from_exp ((continuous_apply i|>.tendsto (0:V)).comp h) ((continuous_apply i|>.tendsto (0:V)).comp k) (hh.mono (fun x hx=> (price _ i).symm.trans ((congr_fun hx i.val).trans (price _ i))))
  filter_upwards [eventually_all.mpr e'] with x hx using funext hx
end
lemma angle_smooth : Tendsto (uncurry (angle (n:=n) (G:=G))) (𝓝 0) (𝓝 0):= aimed angle_germ.continuousAt angle0
lemma group_joins : ∀ᶠ p:R×(R×V) in 𝓝 0, angle (circle p.1 p.2.1) p.2.2=angle p.2.1 (angle p.1 p.2.2):= by
    let d := uncurry (angle (n:=n) (G:=G)); have hF := continuous_fst.tendsto (0:R×R×V); have hS:= continuous_snd.tendsto (0:R×R×V); have h₁ := (continuous_fst.tendsto (0:R×V)).comp hS; have h₂ := (continuous_snd.tendsto (0:R×V)).comp hS; let x:= (uncurry (circle («I»:=Away n) (G:=G))) ∘ (fun p:R×R×V => (p.1,p.2.1)); have hx:Tendsto x (𝓝 0) (𝓝 0):= (aimed join_germ.continuousAt circle0).comp (tup hF h₁)
    apply born (angle_smooth.comp (tup hx h₂)) (angle_smooth.comp (tup h₁ (angle_smooth.comp (tup hF h₂))))
    filter_upwards [(tup hx h₂).eventually physical,(tup h₁ (angle_smooth.comp (tup hF h₂))).eventually physical,(tup hF h₂).eventually physical,(tup hF h₁).eventually mix_gang] with p ha hb hh he
    let a:=p.1; let b:=p.2.1; let v:=p.2.2
    change ignite (angle (circle a b) v)=ignite (angle b (angle a v))
    rw [show ignite (angle (circle a b) v)= play (circle a b) v from ha,show ignite (angle b (angle a v))=play b (angle a v) from hb,play,play,show ignite (angle a v) = play a v from hh]; unfold play; rw [show gang (circle a b)=(gang b* gang a) from funext he]
    funext i; simp only [Lattice.gauge,Pi.mul_apply,mul_inv_rev]; group
end YM.FVA2.Orbit
