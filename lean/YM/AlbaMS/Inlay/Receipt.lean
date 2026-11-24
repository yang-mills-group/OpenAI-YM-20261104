import YM.AlbaMS.Inlay.Temper

/-! # graph transformations of each constituent part.

Translation/folding cases arise with Gauges trivial in Receipt. Signed
hypergroup & pin equivariance checks may include nontrivial colors. In based
drop an L weight moves; Receipt proves propagation for any such factors.
No exact isometry assumptions relating stencil kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay.Net
open Set Function Filter Gauge NormedSpace MeasureTheory Precision LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil
variable {V W I J R : Type*}{G:Gauge}
structure Receipt (G: Gauge) {V W I J : Type*} (Ω : Net V I)(H : Net W J) where
  parcel : V→W
  node : I→Option J
  flip (v:V) : Bool
  color : G.El
  rate : I→ ℝ
  start i : (Ω.head i).bind node= if flip i then H.foot (parcel i) else H.head (parcel i)
  stop i : (Ω.foot i).bind node= if flip i then H.head (parcel i) else H.foot (parcel i)
namespace Receipt
variable {Ω:Net V I}{H:Net W J}(u:Receipt G Ω H)
def inkmap : ink G W→ₗ[ℝ] ink G V := LinearMap.pi fun i=> (sting (u.flip i) (1:ℝ)) • ((G.adjoint u.color) ∘ₗ LinearMap.proj (u.parcel i))
def ghost : ink G J→ₗ[ℝ] ink G I := LinearMap.pi fun i=> G.adjoint u.color ∘ₗ pads (u.node i)
def φ (x:Flit G V)(y:Flit G W) := stip x (u.inkmap (slabQ y))
def ε (x:Flit G I)(y:Flit G J):= stip x (u.ghost (slabQ y))
def skein : Leaf G V I → Leaf G W J → ℝ
| .inl (.inl i),.inl (.inl j)=> u.φ i j
| .inl (.inr i),.inl (.inr j)=> u.φ i j
| .inr (.inl i),.inr (.inl j)=>u.ε i j
| .inr (.inr i),.inr (.inr j)=>u.rate i.1*u.ε i j
| _,_=>0
lemma routed : Routes ø ø u.skein:=by rintro ((i|i)|(i|i)) ((j|j)|(j|j)) h <;> first| rfl | exact False.elim (h rfl)
lemma inkmap_ap (x:ink G W)(i:V): u.inkmap x i=sting (u.flip i) (G.adjoint u.color (x (u.parcel i))):=by
  change sting _ (1:ℝ) • (G.adjoint _ _)=_; cases u.flip i<;> simp
lemma ghost_ap (x:ink G J)(i:I): u.ghost x i=G.adjoint u.color (pads (u.node i) x):=rfl
lemma ghost_opt (x:ink G J)(i:Option I): pads i (u.ghost x)=G.adjoint u.color (pads (i.bind u.node) x):=by
  cases i; change (0:G.Color)=G.adjoint u.color 0; simp; rfl
lemma coasts (v : V)(x:ink G J) : coast Ω v (u.ghost x)= let p:=coast H (u.parcel v) x; let b:=(G.adjoint u.color p.1,G.adjoint u.color p.2); if u.flip v then Prod.swap b else b :=by
  change (pads _ _,pads _ _)=_; rw [u.ghost_opt,u.ghost_opt,u.start,u.stop]; split <;> rfl
lemma natural (x:ink G W)(z:ink G J)(e:V)(he: Quill (x (u.parcel e)))(hc:Quill (G.adjoint u.color (x (u.parcel e))))(H':Quill (u.inkmap x e)):
    Ω.fly (u.ghost z) (u.inkmap x) e=u.inkmap (H.fly z x) e:=by
  change arch (u.inkmap x e) (Ω.coast _ (u.ghost z))=_; rw [u.coasts,u.inkmap_ap,u.inkmap_ap];
  rw [u.inkmap_ap] at H'; simp only; cases h:u.flip e <;> simp only [h, Bool.false_eq_true, ↓reduceIte,sting_false,sting_true,Prod.swap_prod_mk] at H' ⊢ -- fix
  · exact he.brake _ _ hc
  rw [hc.over (p:=(_, _)) (he:=H')]; rw [he.brake (p:=H.coast _ z) (u:=u.color) (he:=hc)] -- sign
  rfl
lemma admap (x y:G.Color): G.adjoint u.color (G.ad x y)=G.ad (G.adjoint u.color x) (G.adjoint u.color y):=by
  apply G.colorMat_injective; rw [G.mat_adjoint,G.colorMat_ad,G.colorMat_ad,G.mat_adjoint,G.mat_adjoint]; have he (x y): G.conjugate u.color (x*y)= G.conjugate u.color x*G.conjugate u.color y:= by
    unfold Gauge.conjugate; simp only [mul_assoc]; generalize hU:G.mat u.color=U; rw [← mul_assoc (star U),show star U*U=1 from hU ▸ G.mat_star_mul _,one_mul]
  rw [← he,← he]; exact map_sub (G.conjugateL u.color) _ _
lemma ghostAd (x y:ink G J) : u.ghost (adI x y)= adI (u.ghost x) (u.ghost y) :=by
  ext1 i; change u.ghost (adI x y) i=G.ad (u.ghost x i) (u.ghost y i); simp_rw [ghost_ap]; cases h:u.node i; change G.adjoint u.color 0=G.ad (G.adjoint u.color 0) (G.adjoint u.color 0); simp; exact u.admap _ _
lemma phi_rule (x:V)(i:G.ColorIndex)(y:Flit G W): u.φ (x,i) y= if u.parcel x=y.1 then sting (u.flip x) (W_adj u.color i y.2) else 0:=by
  unfold Receipt.φ; rw [stip_at,u.inkmap_ap, show slabQ y (u.parcel x)=_ from slab y.1 y.2 _]
  simp only; split -- inspect
  · cases u.flip x <;> simp only [sting_true,sting_false,map_neg] <;> first|rfl| (rw [W_adj,printC,toMatrix_apply]; rfl)
  simp
lemma eps_rule (x:I)(i:G.ColorIndex)(y:Flit G J): u.ε (x,i) y= if u.node x=some y.1 then W_adj u.color i y.2 else 0:=by
  unfold Receipt.ε; rw [stip_at,u.ghost_ap]; simp only; cases h:u.node x with | none=> simp [pads]| some v=>
    simp only [pads, Option.elim_some, proj_apply]; rw [slab y.1 y.2]; by_cases H:v=y.1
    · simp only [H,if_true]; rw [W_adj, printC, toMatrix_apply]; rfl
    simp [H]
variable [Fintype V][Fintype W][Fintype I][Fintype J]
def track : Heave G V I ℝ→ₗ[ℝ] Heave G W J ℝ:= shot Finset.univ u.skein u.routed
omit [Fintype W] [Fintype J] in
lemma times {F G' : Heave G V I ℝ}: u.track (F*G')=u.track F *u.track G':= shot_mul ..
-- Cohort. Tone from shot.
omit [Fintype W] [Fintype J] in
lemma Var (i:Leaf G V I)(j:Leaf G W J): D j (u.track (varC ℝ ø i))=put ø (u.skein i j):=by
  rw [track,shot_D]; simp_rw [drip_apply, varD]; rw [Finset.sum_eq_single i]; rw [if_pos rfl,map_smul, show shot (ρ:=ø) _ _ u.routed 1=1 from shot_put _ _ 1,← put_smul_left,mul_one]; intro a _ hv; rw [if_neg hv,smul_zero]; simp -- simp solves final?
lemma vary (i:Leaf G V I): u.track (varC ℝ ø i) = ∑ j:Leaf G W J,u.skein i j • varC ℝ ø j:=by
  apply deep; rw [sum_read]; change varC ℝ ø i []=_; simp
  intro j; rw [Var, map_sum,Finset.sum_eq_single j]; rw [map_smul, varD,if_pos rfl, ← put_smul_left,mul_one]; intro a _ ha; rw [map_smul,varD,if_neg (Ne.symm ha),smul_zero]; simp
omit [Fintype J] in
lemma action (F:Grove (ink G V)): u.track (bare F)=bare (Brook.dive F u.inkmap.toContinuousLinearMap):=by
  symm; refine Brook.crossed _ _ _ u.skein u.routed F ?_
  rintro ((i|i)|(i|i)) <;> simp only [Fintype.sum_sum_type, skein, zero_smul, smul_zero,map_zero, Finset.sum_const_zero,add_zero] -- may break
  exact (slab_total (u.inkmap (slabQ i))).symm
end Receipt
end YM.MSBar.Inlay.Net
