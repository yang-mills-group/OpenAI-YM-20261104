import YM.SchemeRG11.Flock.Symbol
/-! Axial edge rotation; account the rearward shifts before using symbol. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Flock
open Function Lattice Pert.Bare Maxwell Push.FiniteDetection.Free
variable {E:Type*}[AddCommGroup E][Module ℝ E]
variable {G:Gauge}
def linkup : Bevy E≃ₗ[ℝ] Lattice.Links ℤ E where
 toFun f x:= f x.2 x.1
 invFun f i x:= f (x,i)
 left_inv _:=rfl
 right_inv _:=rfl
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma curled (f:Bevy G.Color)(i j:Axis)(x:Cover) : wideCurl (linkup f) x i j=bend f i j x:=by
 change f i x+f j (x+step i)-f j x-f i (x+step j)=soar i (f j) x-soar j (f i) x; rw [soar_apply,soar_apply]; abel
lemma wingtips (f:Bevy G.Color)(i j:Axis)(n:ℕ)(x:Cover)(v:Fin n→Axis):wideCore G n x (linkup f) i j v=(n.factorial:ℝ)⁻¹ • fleet (clutch v) (bend f i j) x:=by rw [wideCore_apply,clutch_eq]; simp only [curled]
variable (σ : Signed)
def trail (i:Axis):Cover:= if σ.flip i then -step (σ.perm i) else 0
def steer (z:Cover): Module.End ℝ (Plane E) where
 toFun f x:= f (σ.act x+z)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def wing (f:Bevy E):Bevy E:= fun i=> Hyper.flip σ i • steer σ (trail σ i) (f (σ.perm i))
lemma wide_wing(f:Bevy G.Color):wideLink G σ (linkup f)=linkup (wing σ f):=by
 funext e; rcases e with ⟨x,i⟩; rw [wideLink_apply]; cases he:σ.flip i <;> simp [linkup,Lattice.Step.rotate,Lattice.Step.used,wing,Hyper.flip,trail, he,steer,Lattice.posDir,sub_eq_add_neg]
lemma pasted (i:Axis)(x v:Cover)(f:Plane E): soar i (steer σ v f) x= Hyper.flip σ i • soar (σ.perm i) f (σ.act x+v+trail σ i):=by
 have hw:=Step.vec_rotate (d:=posDir i) (R:=ℤ) σ; rw [Step.vec_pos] at hw
 simp only [soar_apply,steer,LinearMap.coe_mk,AddHom.coe_mk,Signed.act_add]
 cases h: σ.flip i
 · simp [Lattice.Step.rotate,Lattice.posDir, Step.vec,h] at hw
   rw [← hw]; simp [trail,Hyper.flip,h,add_right_comm (σ.act _)]
 simp [Lattice.Step.rotate,Lattice.posDir, Step.vec,h] at hw
 rw [← hw]; simp [trail,Hyper.flip,h,add_right_comm (σ.act _)]

def motive(s:Fliers):= (s.map (trail σ)).sum
def stir(s:Fliers):= (s.map (Hyper.flip σ)).prod
lemma prism(s:Fliers)(z:Cover)(f:Plane E): fleet s (steer σ z f)=stir σ s • steer σ (z+motive σ s) (fleet (s.map σ.perm) f):=by
 induction s using Multiset.induction generalizing z f with
 | empty=> simp only [fleet_zero,motive,stir,Multiset.map_zero,Multiset.prod_zero,one_smul,Multiset.sum_zero,add_zero];rfl
 | cons i s ih=>
    rw [fleet_cons']; change fleet s (soar i _) = _
    have hh: soar i (steer σ z f)=Hyper.flip σ i • steer σ (z+trail σ i) (soar (σ.perm i) f) :=by
       funext y; change _= Hyper.flip σ i • soar (σ.perm i) f (σ.act y + (z+trail σ i)); rw [pasted,add_assoc]
    rw [hh,map_smul, ih]; simp only [motive,stir,Multiset.map_cons,Multiset.prod_cons,Multiset.sum_cons,smul_smul,add_assoc,fleet_cons']; rfl
lemma clutch_perm {n:ℕ}(v:Fin n→ Axis) : Multiset.map (σ.perm) (clutch v)=clutch (σ.perm ∘ v) :=by
 induction n with
 | zero=>rw [Multiset.card_eq_zero.mp (cargo v),Multiset.map_zero,Multiset.card_eq_zero.mp (cargo _)]
 | succ n ih=>
    let r:=Fin.tail v; let a:=v 0
    have he:v=Fin.cons a r:=(Fin.cons_self_tail ..).symm
    conv_lhs=>rw [he,tract,Multiset.map_cons,ih r]
    rw [show σ.perm ∘ v=Fin.cons (σ.perm a) (σ.perm ∘ r) from by ext i; refine Fin.cases ?_ ?_ i; rfl; intro k; simp [r]; rfl,tract]
lemma clutch_stir {n:ℕ}(v:Fin n→ Axis):stir σ (clutch v)=∏ i,Hyper.flip σ (v i):=by
 induction n with
 | zero=> rw [Multiset.card_eq_zero.mp (cargo v),Finset.univ_eq_empty,Finset.prod_empty]; rfl
 | succ n ih=>
    rw [←Fin.cons_self_tail v,tract,Fin.prod_univ_succ]; simp only [stir,Multiset.map_cons,Multiset.prod_cons, Fin.cons_zero, Fin.cons_succ]; rw [show (Multiset.map (Hyper.flip σ) (clutch (Fin.tail v))).prod=_ from ih (Fin.tail v)]
lemma orient (f:Bevy E)(s:Fliers)(x:Cover)(i:Axis):
 fleet s (wing σ f i) x=(Hyper.flip σ i*stir σ s) • fleet (s.map σ.perm) (f (σ.perm i)) (σ.act x+(trail σ i+motive σ s)):=by simp only [wing,map_smul,prism,smul_smul];rfl
lemma o_vert (f:Bevy E)(n:ℕ)(h:f∈ spanHull E (n+1))(s:Fliers)(hs:s.card=n)(x:Cover)(i:Axis): fleet s (wing σ f i) x=(Hyper.flip σ i*stir σ s) • fleet (s.map σ.perm) (f (σ.perm i)) 0:=by
 rw [orient]; congr 1; exact landed (member.mp (in_hull.mp h _)) _ (by simp [hs]) _ 0
lemma qwing (f: Bevy G.Color)(n:ℕ)(h:f∈team G.Color (n+2))(x:Cover):
 let P:Shell G n:=⟨leadT n f,conch n f h⟩
 wideCore G n x (wideLink G σ (linkup f))= components (gaugeJet (Hyper.turn σ P)):=by
 intro P; rw [wide_wing]; funext i j v; rw [wingtips]; unfold components; rw [match_leg]
 change _= Hyper.turns σ (leadT n f) i j (basis ∘ v); rw [Hyper.apply_turns]
 unfold bend; rw [_root_.map_sub,Pi.sub_apply]; let s:=clutch v
 have he (v:Fin n→Axis)(i:Axis)(f:Plane G.Color)(x:Cover): fleet (clutch v) (soar i f) x = fleet (i ::ₘ clutch v) f x:=by rw [fleet_cons'];rfl
 have hh (i:Axis): (i ::ₘ clutch v).card=n+1:=by simp [cargo]
 have hp:f∈spanHull G.Color (n+2):= h.1
 let u:=σ.perm ∘ v
 let q:= ∏ k,Hyper.flip σ (v k)
 rw [he,he,o_vert σ f _ hp _ (hh _) _ j,o_vert σ f _ hp _ (hh _) _ i]
 have ht : Hyper.Rₛ σ ∘ basis ∘ v= fun k=> Hyper.flip σ (v k) • (basis ∘ u) k := funext fun i=> Hyper.moves_basis ..
 rw [ht,(leadT n f _ _).map_smul_univ,leadT,print_tip]
 have hs (i:Axis) : stir σ (i ::ₘ clutch v)= Hyper.flip σ i*q:=by simp only [stir,Multiset.map_cons,Multiset.prod_cons]; rw [show (Multiset.map (Hyper.flip σ) (clutch v)).prod=q from clutch_stir ..]
 simp only [bend,map_sub,Pi.sub_apply,he,hs,Multiset.map_cons,clutch_perm]
 simp only [smul_sub,smul_smul,Hyper.sign₂]; congr 2 <;> try dsimp only [u,q]; ring
lemma width (f:Bevy G.Color)(n:ℕ)(h:f∈team G.Color (n+2))(x:Cover): wideLinear G n 1 x (linkup f)=gaugeJet ⟨leadT n f,conch n f h⟩:=by
 let P:Shell G n:=⟨_,conch n f h⟩; have he (s:Signed):Labels.Taylor.turn s.ortho (radialMap (wideCore G n (affine s⁻¹ 0 x) (wideLink G s (linkup f))))=gaugeJet P:=by
    rw [qwing s f n h]; change Labels.Taylor.turn _ (radialize (components (gaugeJet (Hyper.turn _ P)))) =_; rw [complete, Hyper.gaugeTurn, ← Labels.Taylor.turn_mul]; simp
 simp only [wideLinear,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,one_zpow,one_smul,he, Finset.sum_const,Finset.card_univ]
 rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
lemma width_zero (f:Bevy G.Color)(n:ℕ)(h:f∈team G.Color (n+1))(x:Cover): wideLinear G n 1 x (linkup f)=0:=by
 rw [width f n (team_height (by omega) h)]
 apply Eq.trans _ gaugeJet.map_zero; apply congrArg _; apply Subtype.ext; funext i j
 refine tipped _ _ (fun v=>?_); unfold leadT; rw [print_tip,bend,map_sub,Pi.sub_apply]
 have H (i j:Axis) : fleet (clutch v) (soar i (f j))=0:=member.mp (soar_lower _ _ (team_wing h j) i) _ (cargo _)
 rw [H,H]; simp
end YM.SchemeRG11.Flock
