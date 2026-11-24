import YM.AlbaMS.Inlay.Inc

/-!
# Native BV for graph links

Core before Wave renorm. Compute head/tail based fields, includes *actual* local
Jacobians of Haar for the given chart. Rotation of all color slots coherent for
entire graph. Prove Ward via Lie-group gauging; applies without simply marking
invariant jets or Mum. Other choices of gauge-fix not considered here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay
open Set Function Filter Gauge NormedSpace MeasureTheory Precision LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil
variable {G : Gauge} {V I J R : Type*}
abbrev pathof (G:Gauge)(V I:Type*): Brook (@ø (Flit G V) (Flit G I)) (ink G V) where
  stream i:=match i with| .inl (.inl x)=>slabQ x| _=>0
  empty := by rintro ((v|v)|(i|i)) H <;> first| exact Bool.noConfusion H|rfl
namespace Net
variable (Ω : Net V I)
def coast (e:V): ink G I→ₗ[ℝ] faces G:= (pads (Ω.head e)).prod (pads (Ω.foot e))
abbrev boat (i:Option I)(u:I→G.El): G.El:=i.elim 1 u
def current (x:ink G V): ink G I→ₗ[ℝ] ink G V:= LinearMap.pi fun e=> arch (x e) ∘ₗ Ω.coast e
def home (u:I→G.El)(U:V→G.El)(e:V): G.El:= boat (Ω.head e) u*U e*(boat (Ω.foot e) u)⁻¹
def Honor (W:(V→G.El)→R):Prop:= ∀ U u,W (Ω.home u U)= W U
def fromWax (W:(V→G.El)→ℝ): ink G V→ℝ:= fun A=> W (G.lieExp ∘ A)
lemma current_apply (x:ink G V)(u:ink G I)(e: V): current Ω x u e=arch (x e) (Ω.coast e u):=rfl
lemma coaster (u v: ink G I)(e:V): coast Ω e (adI u v)=(G.ad (Ω.coast e u).1 (Ω.coast e v).1,G.ad (Ω.coast e u).2 (Ω.coast e v).2):= by
  have he (i:Option I): pads i (adI u v)= G.ad (pads i u) (pads i v):=by cases i; change 0=G.ad 0 0; simp; rfl
  exact Prod.ext (he _) (he _)
lemma warped (t:ℝ)(A:ink G V)(u:ink G I): (fun e=> warp t (Ω.coast e u) (G.lieExp (A e))) = Ω.home (fun i=> G.lieExp (t • -(u i))) (G.lieExp ∘ A):=by
  funext i; unfold warp; have hh (x:Option I): G.lieExp (t • -(pads x u))=boat x (fun i=> G.lieExp (t • -(u i))):=by cases x; simp [pads,boat]; rfl
  have hp x : G.lieExp (t • (pads x u))=(boat x (fun i=> G.lieExp (t • -(u i))))⁻¹:=by rw [← hh,smul_neg, Work.F03.exp_neg_color,inv_inv]
  change G.lieExp (t • -(pads _ u))*_*G.lieExp (t • pads _ u)=_; rw [hh,hp]; rfl
end Net

variable [Fintype V][Fintype I]
def Queue (F:ink G V→ℝ):Prop:= ContDiffAt ℝ ω F 0
def bare (F:Grove (ink G V)): Heave G V I ℝ:= (pathof G V I).shine F
omit [Fintype I] in
lemma bare_h (F:Grove (ink G V)): EvenT (bare (I:=I) F):= (pathof G V I).bright F
omit [Fintype I] in
lemma bare_simple (F:Grove (ink G V)): SimpleT (bare (I:=I) F):= ⟨⟨fun _=>(pathof G V I).evaporate F rfl, fun _=> (pathof G V I).evaporate F rfl⟩, fun _=> (pathof G V I).evaporate F rfl⟩

namespace Net
variable (Ω : Net V I)
def fly (u:ink G I)(x:ink G V):= Ω.current x u
omit [Fintype I] in
lemma wax_rate {A:ink G V}(h: ∀ e, Quill (A e))(u:ink G I): ContDiffAt ℝ ω (Ω.fly u) A:=
  contDiffAt_pi.mpr fun i=> (Quill.smooth (h i) (Ω.coast i u)).comp (f:=ContinuousLinearMap.proj i) A (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : V=> G.Color) i).contDiff.contDiffAt
omit [Fintype I] in
lemma sees {A:ink G V}(h:∀ e,Quill (A e))(u:ink G I)(y: ink G V)(e:V): (fderiv ℝ (Ω.fly u) A y) e= fderiv ℝ (fun x=> arch x (Ω.coast e u)) (A e) (y e):= by
  let Z:=fun x=> arch x (Ω.coast e u); let L:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : V=> G.Color) e
  have H:= L.hasFDerivAt.comp A ((Ω.wax_rate h u).differentiableAt (by simp)).hasFDerivAt; have ht:= (((Quill.smooth (h e) (Ω.coast e u)).differentiableAt (by simp)).hasFDerivAt).comp A (show HasFDerivAt L _ _ from L.hasFDerivAt)
  exact DFunLike.congr_fun (H.unique ht) y
-- expose
abbrev spotG (x : Flit G I) (i : Flit G V): Grove (ink G V):= ⟨stip i ∘ Ω.fly (slabQ x),
    (stip i).toContinuousLinearMap.contDiff.contDiffAt.comp (f:=Ω.fly (slabQ x)) (0:ink G V) (Ω.wax_rate (fun _=> (quill G).self_of_nhds) _)⟩
abbrev chat (x : Flit G I)(i : Flit G V) : Heave G V I ℝ:= bare (spotG Ω x i)
variable (F:Grove (ink G V))
omit [Fintype I] in
lemma waters (x: Flit G I)(g : Grove (ink G V))(hg:g.val=ᶠ[𝓝 0] fun A=> fderiv ℝ F.val A (Ω.fly (slabQ x) A)) : impulse (chat Ω) x (bare F)=bare g:=by
  let C:=pathof G V I; let U:=Ω.spotG x
  change (∑ i:Flit G V,C.shine _*DA i (C.shine F))=C.shine g
  symm; apply Eq.trans (C.flash _ Finset.univ (fun i : Flit G V=> U i*dx (slabQ i) F) ?_) (Finset.sum_congr rfl (fun i _=>?_))
  · filter_upwards [hg] with y h; rw [h]
    nth_rw 1 [← slab_total (Ω.fly (slabQ x) y)]; rw [map_sum]; simp_rw [map_smul,Finset.sum_apply]; rfl
  rw [Brook.gleam_mul]; rfl

omit [Fintype I] in
private lemma during {A:ink G V}(h:∀ i,Quill (A i))(p q:ink G I): fderiv ℝ (Ω.fly q) A (Ω.fly p A)- fderiv ℝ (Ω.fly p) A (Ω.fly q A)= Ω.fly (adI p q) A:=by
  ext1 i; rw [Pi.sub_apply,Ω.sees h,Ω.sees h]; change _ - _=arch _ (coast Ω i _); rw [Ω.coaster]; exact arch_com (h i) ..
-- can generalize illumination along any A; current needs only comm & measure identities at zero.
omit [Fintype I] in
lemma tide : ∀ᶠ A:ink G V in 𝓝 0, ∀ i, Quill (A i):= by
  apply eventually_all.mpr; intro i; exact ((continuous_apply i).tendsto (0:ink G V)).eventually (quill G)
omit [Fintype I] in
def ray (p:ink G I) (F:Grove (ink G V)): Grove (ink G V):= ⟨fun y=> fderiv ℝ F.val y (Ω.fly p y), (F.2.fderiv_right (by simp)).clm_apply (Ω.wax_rate (fun _=>(quill G).self_of_nhds) _)⟩
lemma wade (x y:Flit G I)(i:Flit G V): impulse Ω.chat x (Ω.chat y i)-impulse Ω.chat y (Ω.chat x i)=∑ j:Flit G I,(grit G I).price x y j • Ω.chat j i:=by
  let X:=slabQ x; let Y:=slabQ y; let F:= ray Ω X (spotG Ω y i); let H:=ray Ω Y (spotG Ω x i); let C:=pathof G V I
  rw [waters Ω _ _ F (Filter.EventuallyEq.refl ..),waters Ω _ _ H (Filter.EventuallyEq.refl ..)]; change C.shine F-C.shine H=_; rw [← Brook.gleam_sub];
  refine Eq.trans (C.flash _ Finset.univ (fun j:Flit G I=> (grit G I).price x y j • Ω.spotG j i) ?_) (Finset.sum_congr rfl (fun _ _=> C.gleam_smul ..))
  filter_upwards [tide (G:=G) (V:=V)] with A h -- fix
  have he (z:Flit G I)(q:ink G V): fderiv ℝ (Ω.spotG z i).val A q= stip i (fderiv ℝ (Ω.fly (slabQ z)) A q):=by
    change fderiv ℝ ((stip i).toContinuousLinearMap ∘ _) _ _=_; rw [fderiv_comp _ (stip i).toContinuousLinearMap.differentiableAt ((Ω.wax_rate h _).differentiableAt (by simp)),(stip i).toContinuousLinearMap.fderiv]; rfl
  change fderiv ℝ (Ω.spotG y i).val A (Ω.fly X A)- fderiv ℝ (Ω.spotG x i).val A (Ω.fly Y A)= _; rw [he,he,← map_sub, Ω.during h]; change stip i (Ω.current A (adI X Y))=_; rw [← slab_total (adI X Y)]; simp_rw [map_sum,map_smul, Finset.sum_apply,grit_price]; rfl
end Net
end YM.MSBar.Inlay
