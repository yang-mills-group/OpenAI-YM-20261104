import YM.Frontier6.Bouquet.Patron.Staging

/-! Translate the very same exact counterterm vectors to the other
 insertion centers. Use projections only where their orbit sampling is
 defined. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Filter Set Finset Ensemble MeasureTheory Normal Spec Road Forest Tale
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(x:E4)
def lands (S:Table C.book)(x:E4): Blueprint S →+ Blueprint S where
    toFun y:= y.map (fun i=> (i.fst+x,i.snd))
    map_zero':=by simp
    map_add' u v:= Multiset.map_add ..
def landed (S:Table C.book)(x:E4): Spelling S→ₗ[ℂ] Spelling S:= AddMonoidAlgebra.mapDomainLinearMap ℂ ℂ (lands S x)
lemma landed_ring (S:Table C.book): (landed S x : Spelling S→ Spelling S)= AddMonoidAlgebra.mapDomainRingHom ℂ (lands S x):=rfl
lemma carrying (z:E4)(v:S.Tag): landed S x (Tale.letter S z v)=Tale.letter S (z+x) v:= by unfold Tale.letter landed press; rw [AddMonoidAlgebra.mapDomainLinearMap_single]; rfl
lemma convoy {V:Type}[Fintype V](z:V→ E4)(v:V→ S.Tag): landed S x (assembly S z v)=assembly S (fun i=> z i+x) v:=by unfold assembly; rw [landed_ring,map_prod]; apply prod_congr rfl; intro i _; exact carrying ..
lemma travels (d:ℕ)(z:E4)(v:S.Field d): landed S x (suit K z d v)= suit K (z+x) d v:=by rw [suit_eq, suit_eq,map_sum];simp_rw [map_smul,carrying]
lemma poses (A:Spelling S)(s:StateIndex K): poll S (state K s) (landed S x A)=poll S (state K s) A:= by
    induction A using AddMonoidAlgebra.induction_linear with
    | zero=> simp
    | add a b ih jh=> rw [map_add,map_add,map_add,ih,jh]
    | single p a=>
       obtain ⟨n,y,h⟩:=exists_enum S p; let f:=Prod.fst ∘ y; let v:= Prod.snd ∘ y;
       have he : AddMonoidAlgebra.single p a=a • assembly S f v:=by rw [assemble_eq,press,AddMonoidAlgebra.smul_single]; change _= AddMonoidAlgebra.single (arrange y) (a*1); rw [h,mul_one]
       rw [he,map_smul,map_smul,map_smul,convoy, translating K]
lemma illumination_shift (p:Spelling S) (a:E4) : Tale.written K (a+x) (landed S x p)=Tale.written K a p:=by
   funext s n y v; change poll S (state K s) (_* assembly S _ _) = poll S (state K s) (p*assembly S _ _); let z:= fun i=> y i + a; rw [← poses K x (p*assembly S z v) s]; rw [show landed S x (p*assembly S z v)=landed S x p*landed S x (assembly S z v) from map_mul (AddMonoidAlgebra.mapDomainRingHom ℂ (lands S x)) p _,convoy]; congr 2; apply congr_arg (fun y'=> assembly S y' v); ext1 i; exact (add_assoc ..).symm -- congr a
lemma shifts_cost {p:Spelling S}(a:E4)(d:ℕ)(he: Visible K a d p): StageWeight K (a+x) d (landed S x p)= StageWeight K a d p:=by
   have hv:= illumination_shift K x p a; rw [stage_weight K d he,stage_weight K d (show Visible K (a+x) d (landed S x p) by unfold Visible; rw [hv];exact he)]; unfold Forest.pitch absorb; rw [hv]
end YM.Frontier6.Bouquet
