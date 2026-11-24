import YM.RegulatorIR.Quadratic.Chute

/-!
# At the top, fold of literal translation stencil $K$

Restrict on equivariant links: orbit energy has the HALF because the measure
is on unoriented representatives; K fold correspondingly *not* halved. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Quadratic
open Lattice Function Budget Motion Budget.Layer Budget.Packet Budget.Deck Step Diagram RG Binding Filter Tree Tree.Forest Metric Set Geometry Geometry.Field PertExtension Chart Laplace GaussianScore Matrix Wilson Orb Series PertExtension.Series.Radial Diagram.Formal Exterior
open scoped NNReal ENNReal Topology Real Classical BigOperators ContDiff PowerSeries Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{X Y:Type}{P:ℝ}{f:Side}
section Top

def sun (x:Cover)(a:PlaqAxes)(i:X) : Long X →₀ ℝ:= let u:=a.val.1; let v:=a.val.2; Finsupp.single ((x,u),i) 1+ Finsupp.single ((x+step u,v),i) 1-Finsupp.single ((x+step v,u),i) 1- Finsupp.single ((x,v),i) 1

def dream (e:Edge Cover) (a:PlaqAxes)(i:X) : Long X→₀ ℝ:= let u:=a.val.1;let v:=a.val.2; (if e.2=u then sun e.1 a i-sun (e.1-step v) a i else 0)+(if e.2=v then sun (e.1-step u) a i-sun e.1 a i else 0)
def moon (p:Long X) : Long X →₀ ℝ:=∑ a:PlaqAxes, dream p.1 a p.2

-- torus projection

def mist (e:Edge (Site f))(a:PlaqAxes) (x:Horizon G f)(i:G.ColorIndex):= let u:=a.val.1;let v:=a.val.2; (if e.2=u then plume x (e.1,a) i-plume x (e.1-step v,a) i else 0)+(if e.2=v then plume x (e.1-step u,a) i-plume x (e.1,a) i else 0)
lemma plume_flip (x:Horizon G f)(h:Even f.val)(p: Site f)(a:PlaqAxes): plume x (-p-step a.val.1-step a.val.2,a)=plume x (p,a):=by
 let q:=fire x; let u:=a.val.1; let v:=a.val.2; let p':=-p-step u-step v
 change q (p',u)+q (p'+step u,v)-q (p'+step v,u)-q (p',v)=q (p,u)+q (p+step u,v)-q (p+step v,u)-q (p,v)
 have hz y:q (reflect y)= -q y:= fire_swaps x h y
 rw [show (p',u)=reflect (p+step v,u) by unfold reflect p'; simp;abel,
     show (p'+step u,v)=reflect (p,v) by unfold reflect p'; simp;abel,
     show (p'+step v,u)=reflect (p,u) by unfold reflect p'; simp; try abel,
     show (p',v)=reflect (p+step u,v) by unfold reflect p'; simp;abel,hz,hz,hz,hz];abel
lemma mist_inv (h:Even f.val)(x:Horizon G f)(e)(a i) : mist (reflect e) a x i= -mist e a x i:=by
 let u:=a.val.1; let v:=a.val.2
 rcases e with ⟨p,l⟩
 unfold mist;dsimp only [Orb.reflect]; have hp:u<v:= a.property; change ((if l=u then (plume x (_,a)) i-plume x (_,a) i else _) + (if l=v then _ else _)) = -((if l=u then _ else _)+(if l=v then _ else _))
 by_cases h':l=u
 · subst l; rw [if_pos rfl,if_pos rfl,if_neg hp.ne, if_neg hp.ne, add_zero,add_zero,
    show -p-step u= -(p-step v)-step u-step v by abel, plume_flip x h,show -(p-step v)-step u-step v-step v= -p-step u-step v by abel, plume_flip x h];abel
 rw [if_neg h',if_neg h']
 by_cases H:l=v
 · subst l; rw [if_pos rfl, if_pos rfl,zero_add,zero_add,show -p-step v-step u= -p-step u-step v by abel,plume_flip x h,show -p-step v= -(p-step u)-step u-step v by abel,plume_flip x h];abel
 rw [if_neg H,if_neg H,zero_add,neg_zero]

variable {l:ℝ}(H:Even f.val)(hz:l*f.val=P)(x:Horizon G f)
local notation "g" => bridge (Carto G l P H hz) (paper G f x)
lemma sun_v (v:Cover)(a:PlaqAxes)(i:G.ColorIndex):combo g (sun v a i)=plume x (wrap f v,a) i:=by
 simp only [sun,map_sub,map_add,combo,Finsupp.linearCombination_single,one_smul]; simp_rw [firebrand];simp only [around,map_add,wrap_step]; rfl
lemma dream_v (e:Edge Cover)(a i) : combo g (dream e a i)=mist (around f e) a x i:=by rcases e with ⟨v,j⟩; simp only [dream,mist,around]; split_ifs <;> simp only [map_sub,map_add,map_zero] <;> simp [sun_v,wrap_step]
lemma moon_v (e:OEdge f)(i:G.ColorIndex) : (fmat (Carto G l P H hz) (Carto G l P H hz) (finer moon) *ᵥ paper G f x) (e,i)=∑ a,mist e.val a x i:=by
 rw [frontier];change combo g (∑ a:PlaqAxes,dream (Geometry.position e) a i)= _;rw [map_sum];simp_rw [dream_v,position_edge]

-- finite IBP counting
lemma mist_bilinear (x y:Horizon G f)(a:PlaqAxes) (i:G.ColorIndex):
 (∑ e:Edge (Site f),fire x e i*mist e a y i)=∑ p: Site f, plume x (p,a) i*plume y (p,a) i :=by
 let u:=a.val.1; let v:=a.val.2; let A(p:Site f):= (fire x (p,u)) i; let B(p:Site f):= (fire x (p,v)) i; let F(p:Site f):=plume y (p,a) i
 have hp (p:Site f): (∑ j:Axis,fire x (p,j) i*mist (p,j) a y i)=A p*F p+B p*F (p-step u)-(A p*F (p-step v)+B p*F p):=by
    simp_rw [mist]; simp only [mul_add,mul_ite,mul_zero, Finset.sum_add_distrib,Finset.sum_ite_eq', Finset.mem_univ,if_true]; unfold A B F u v;ring
 have hx (U L:Site f→ℝ)(m:Site f) : (∑ p,U p*L (p-m))=∑ p,U (p+m)*L p:=by
    rw [← Equiv.sum_comp (Equiv.addRight m) (fun p=> U p * L (p-m))]; exact Finset.sum_congr rfl fun p _=>by simp
 rw [Fintype.sum_prod_type];simp_rw [hp];rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib,hx B F,hx A F, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
 apply Finset.sum_congr rfl;intro p _; have hs:plume x (p,a) i=A p+B (p+step u)-A (p+step v)-B p:=rfl; rw [hs]; unfold F; ring

def both (H:Even f.val) : OEdge f⊕ OEdge f≃ Edge (Site f):=by
 let L : OEdge f⊕ OEdge f→ Edge (Site f):= Sum.elim Subtype.val fun q=> reflect q.val
 refine Equiv.ofBijective L ⟨?_,?_⟩
 · have h (a b:OEdge f): b.val≠ reflect a.val:=by intro hb; have ht:=b.property; rw [hb,eR_reflect,a.property] at ht; exact no_fixed_edge H _ ht.symm
   rintro (i|i) (j|j) he
   · exact congr_arg Sum.inl (Subtype.ext he)
   · exact (h j i he).elim
   · exact (h i j he.symm).elim
   exact congr_arg Sum.inr (Subtype.ext ((show Function.Involutive (reflect (n:=f)) from reflect_reflect).injective he)) -- Function.Involutive ...
 intro x; rcases eR_spec x with h|h
 · exact ⟨.inl (index x),h⟩
 have hp: (index x).val=reflect x:=h; exact ⟨.inr (index x), (congr_arg reflect hp).trans (reflect_reflect _)⟩
include H in
lemma doubles {T:Edge (Site f)→ℝ}(h:∀ i,T (Orb.reflect i)=T i) : (∑ i:Edge (Site f),T i)=2*∑ i:OEdge f,T i.val:=by rw [← (both H).sum_comp T, Fintype.sum_sum_type];change _+(∑ i:OEdge f,T (Orb.reflect i.val))=_;simp_rw [h]; rw [two_mul]; rfl
lemma shine (x y:Horizon G f) :
 2*(paper G f x ⬝ᵥ (fmat (Carto G l P H hz) (Carto G l P H hz) (finer moon) *ᵥ paper G f y))= ∑ p:Face (Per f), ∑ i:G.ColorIndex,plume x p i*plume y p i:=by
 let M(e : Edge (Site f)) (i:G.ColorIndex) (a:PlaqAxes):= fire x e i*mist e a y i
 have hp: (∑ e: Edge (Site f),∑ i,∑ a, M e i a)=∑ i:G.ColorIndex, ∑ a:PlaqAxes, ∑ p:Site f,plume x (p,a) i*plume y (p,a) i:=by
    rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro i _;rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro a _; exact mist_bilinear x y a i
 rw [dotProduct,Fintype.sum_prod_type];simp_rw [moon_v]
 have he : (∑ e:Edge (Site f),∑ i,∑ a,M e i a)=2*∑ e:OEdge f,∑ i,∑ a,M e.val i a:=by
    apply doubles H; intro z; apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro a _; unfold M; rw [fire_swaps x H,mist_inv H, PiLp.neg_apply,neg_mul_neg]
 have hs (e:OEdge f) (i:G.ColorIndex): paper G f x (e,i)*(∑ a,mist e.val a y i)=∑ a,M e.val i a:=by unfold M; rw [fire_at,Finset.mul_sum];rfl
 simp_rw [hs]; rw [← he,hp,Fintype.sum_prod_type,Finset.sum_comm]
 conv_rhs=> rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro a _; rw [Finset.sum_comm]
lemma shines : (fmat (Carto G l P H hz) (Carto G l P H hz) (finer moon)).transpose=fmat (Carto G l P H hz) (Carto G l P H hz) (finer moon):=by
 ext i j; let p:= Carto G l P H hz;let e (i:Book G f) : Horizon G f:= (paper G f).symm (Pi.single i 1); let T:= fmat p p (finer moon)
 have he (i j : Book G f) : 2*T i j =∑ p:Face (Per f),∑ b:G.ColorIndex,plume (e i) p b*plume (e j) p b:= by
    rw [← shine H hz]; unfold e; rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,dotProduct_comm (Pi.single i _),dotProduct_single_one]; exact congr_arg (fun x:ℝ=>2*x) (dotProduct_single_one _ j).symm
 have hp : T j i=T i j:= mul_left_cancel₀ (two_ne_zero (α:=ℝ)) (by rw [he j,he i]; apply Finset.sum_congr rfl;intro l _; exact Finset.sum_congr rfl (fun _ _=> mul_comm ..))
 exact hp
lemma sunrise : beneath (fmat (Carto G l P H hz) (Carto G l P H hz) (finer moon))=costO:=by
 ext1 x; have hp:= shine H hz x x; unfold beneath phase;unfold costO; simp_rw [EuclideanSpace.real_norm_sq_eq,← Finset.sum_div];simp_rw [← sq] at hp;rw [← hp]; ring
end Top
end YM.RegulatorIR.Quadratic
