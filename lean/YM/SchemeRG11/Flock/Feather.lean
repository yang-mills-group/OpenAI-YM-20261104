import YM.SchemeRG11.Flock.Furl
/-! Filtered cover colors. Coefficient engineering coordinate is scalar;
 vertical frame may be redundant. -/
noncomputable section
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
set_option autoImplicit false
namespace YM.SchemeRG11.Flock
open Function Lattice
abbrev Class (m:ℕ):=team ℝ (m+1)
abbrev TurnArray(m:ℕ):=Axis→Axis→(Fin m→Axis)→ℝ
def starboard (m:ℕ):Submodule ℝ ↥(Class m) where
 carrier :={f|skim m f.val}
 zero_mem':=by intro i j s h; simp [bend]
 add_mem':=by
   rintro f g hf hg i j s h; have H:bend (f+g).val i j=bend f.val i j+bend g.val i j:=by simp only [bend,Submodule.coe_add,Pi.add_apply,map_add]; abel
   rw [H,map_add, Pi.add_apply,hf i j s h,hg i j s h,add_zero]
 smul_mem':=by rintro c f hf i j s h; simp only [bend,Set.mem_setOf_eq, skim,Submodule.coe_smul,Pi.smul_apply,map_smul,← smul_sub] at *; rw [hf i j s h, smul_zero]
def exhib (m:ℕ): Submodule ℝ ↥(Class m):= Classical.choose (exists_isCompl (starboard m)) -- check
lemma exh (m:ℕ): IsCompl (starboard m) (exhib m):= Classical.choose_spec (exists_isCompl (starboard m))
def slip (m:ℕ):Submodule ℝ (Plane ℝ):= cap ℝ (m+2) ⊓ lap.ker
instance (m:ℕ):FiniteDimensional ℝ (slip m):=FiniteDimensional.of_injective (Submodule.inclusion (show slip m ≤ cap ℝ (m+2) from inf_le_left)) (Submodule.inclusion_injective _)
abbrev HIndex(m:ℕ):=Fin (Module.finrank ℝ (exhib m))
abbrev VIndex(m:ℕ):=Fin (Module.finrank ℝ (slip m))
local instance (m:ℕ) : Module.Free ℝ (exhib m):=by
  exact @Module.Free.of_divisionRing ℝ ↥(exhib m) _ _ _
abbrev transverse(m:ℕ):=Module.finBasis ℝ (exhib m)
abbrev riseB (m:ℕ):=Module.finBasis ℝ (slip m)
def hor {m:ℕ}(i:HIndex m):Class m:=(transverse m i).val
abbrev vertPot {m:ℕ}(i:VIndex m): Plane ℝ:=(riseB m i).val
def vert {m:ℕ}(i:VIndex m):Class m:= ⟨_,team_incline (riseB m i).property.1 (riseB m i).property.2⟩
abbrev Tail (m:ℕ) := HIndex m ⊕ VIndex m
def tuft {m:ℕ}(i:Tail m): Class m:=Sum.elim (hor (m:=m)) (vert (m:=m)) i
lemma gust (m:ℕ)(f:Bevy ℝ)(h:f∈ Class m): ∃ b: Tail m→ℝ, f-∑ i:Tail m,b i • (tuft i).val ∈ team ℝ m:=by
 have ht: (⟨f,h⟩:Class m)∈ starboard m ⊔ exhib m :=by rw [(exh m).sup_eq_top]; simp
 obtain ⟨g,G,t,Q,e⟩ := Submodule.mem_sup.mp ht
 let C:HIndex m→ℝ:=(transverse m).equivFun ⟨t,Q⟩
 have hz:t.val = ∑ i:HIndex m,C i • (hor i).val:=by
   have H:=congrArg (fun x:exhib m=>(x.val :Class m).val) ((transverse m).sum_repr (⟨t,Q⟩:exhib m)); rw [AddSubmonoidClass.coe_finsetSum,AddSubmonoidClass.coe_finsetSum] at H; exact H.symm
 obtain ⟨v,V,K,H⟩:=team_exact m g.val g.property G
 let c:VIndex m→ℝ:=(riseB m).equivFun (⟨v,V,K⟩:slip m)
 have hp: v=∑ i:VIndex m,c i • vertPot i:=by
   have w:=congrArg (Subtype.val ∘ (_root_.id (α:=↥(slip m)))) ((riseB m).sum_repr ⟨v,V,K⟩)
   simp only [_root_.id_eq,comp_apply,AddSubmonoidClass.coe_finsetSum] at w; exact w.symm
 refine ⟨Sum.elim C c,?_⟩
 have hh : ∑ i:Tail m,(Sum.elim C c i:ℝ) • (tuft i).val=t.val+incline v:=by
   rw [Fintype.sum_sum_type,hz,hp,map_sum]; simp only [map_smul];rfl
 rw [hh,show f=g.val+t.val from (congrArg Subtype.val e).symm,sub_eq_add_neg,neg_add_rev]; apply Eq.mp _ H; congr 1; abel
lemma deflate_zero: IsEmpty (HIndex 0):=by
 constructor; intro i
 have hp: hor (m:=0) i=0:= (Submodule.disjoint_def.mp (exh 0).disjoint) _ (by intro i j s H; omega) (transverse 0 i).property
 exact (Module.Basis.ne_zero (transverse 0) i) (Subtype.ext hp)
def gauges (m:ℕ): exhib (m+1) →ₗ[ℝ] TurnArray m where
 toFun g a b v:= (m.factorial:ℝ)⁻¹ * fleet (clutch v) (bend g.val.val a b) 0
 map_add' f g:=by funext i j v; simp [bend, add_sub_add_comm,mul_add]
 map_smul' c f:=by funext i j v; simp only [bend,Submodule.coe_smul,Pi.smul_apply,map_smul,← smul_sub, smul_eq_mul,RingHom.id_apply]; ring
lemma pilot (m:ℕ) : ∃ R: TurnArray m→ₗ[ℝ] (HIndex (m+1)→ℝ),∀ i:HIndex (m+1),R (gauges m ((transverse (m+1)) i))=Pi.single i 1:=by
 obtain ⟨r,h⟩:=LinearMap.exists_leftInverse_of_injective (K:=ℝ) (V:=exhib (m+1)) (V':=TurnArray m) (gauges m) (LinearMap.ker_eq_bot'.mpr (by
     intro f hf
     apply Subtype.ext
     apply Submodule.disjoint_def.mp (exh (m+1)).disjoint _ ?_ f.property
     intro i j s hs
     obtain ⟨p,rfl⟩:= gather s (show s.card=m by omega)
     have hh:=congrFun (congrFun (congrFun hf i) j) p
     change ((_ :ℝ)⁻¹ * _)=0 at hh; exact (mul_eq_zero.mp hh).resolve_left (by positivity)))
 refine ⟨(transverse (m+1)).equivFun.toLinearMap ∘ₗ r,fun i=>?_⟩; rw [LinearMap.comp_apply,show r (gauges m _)=_ from LinearMap.congr_fun h _]; simp; ext j; by_cases h:j=i<;>simp [h]

abbrev Feather (n:ℕ):=(m: Fin n) × Tail m.val
abbrev degree {n:ℕ}(v:Feather n) := v.1.val+1
abbrev finch {n:ℕ}(v:Feather n):= (tuft v.2).val
lemma finched {n:ℕ}(v:Feather n): finch v∈ team ℝ (degree v):= (tuft v.2).property
lemma flood {n m:ℕ}(h:m≤n)(f:Bevy ℝ)(hf:f∈ team ℝ m): ∃ x: Feather n→ℝ,(∀i,m<degree i→x i=0) ∧ f= ∑ i:Feather n,x i • finch i:=by
 induction m generalizing f with
 | zero=>
   refine ⟨0,fun _ _=>rfl, ?_⟩; simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero]; funext i; have hx:=team_wing hf i; rw [groundZero] at hx; exact hx
 | succ m ih=>
   obtain ⟨b,hb⟩:=gust m f hf
   obtain ⟨x,hx,H⟩:=ih (by omega) _ hb
   let a:Fin n:= ⟨m,h⟩; let y(k:Fin n):Tail k.val→ ℝ:=Pi.single (M:=fun k:Fin n=>Tail k.val→ℝ) a b k
   have he : ∑ i:Feather n,y i.1 i.2 • finch i = ∑ i:Tail m, b i • (tuft i).val:=by
        rw [Fintype.sum_sigma,Finset.sum_eq_single a]; simp only [y,Pi.single_eq_same]; rfl -- check
        · intro u _ he; apply Finset.sum_eq_zero; intro v _; simp [y,Pi.single_eq_of_ne he]
        simp
   refine ⟨fun i=>x i+y i.1 i.2,fun i ip=>?_,?_⟩
   · have hg:i.1 ≠ a:=fun w=>by unfold degree at ip; rw [w] at ip; exact lt_irrefl _ ip
     change x i+y i.1 i.2=0; rw [hx i (by omega)]; simp [y,Pi.single_eq_of_ne hg]
   rw [sub_eq_iff_eq_add] at H; rw [H,←he]; simp only [add_smul,Finset.sum_add_distrib]
end YM.SchemeRG11.Flock
