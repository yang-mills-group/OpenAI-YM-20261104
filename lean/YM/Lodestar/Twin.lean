import YM.Next.MULTISOURCE.Formal
import YM.Overlay.Terminal
/-!
 # Tag unfolding without highest-arity costs.

 For the replicated discrepancy we'll let EACH actual mark spend two post marks
 with the same center. This allows propagation after subtraction through the
 priced zero-singleton Gate. Need occupancy for both marks (don't claim Drake
 for duplicated centers). Exact only on the full census here (no ideal of other
 exclusions interacting with the injection). Includes quiet and all partial
 modes; no change of normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Lodestar
open Finset Function Marker
open scoped BigOperators Classical Topology
variable {V:Type} [Fintype V] [DecidableEq V]

abbrev Marks (V:Type) [Fintype V] [DecidableEq V] := Stock.census V
-- specifically the ordering (V,Bool) of Cask.Duel -- no overwrite

/-- Keep both twin tags on the whole coefficient. -/
def two (i : (Marks V).Mode) : (Marks (V×Bool)).Mode := ⟨i.val.product univ,mem_univ _⟩

lemma two_test (i:(Marks V).Mode) (v:V) (b:Bool) : (v,b)∈(two i).val ↔ v∈i.val:= by simp [two]
lemma two_inj : Injective (two (V:=V)):= by
   intro i j h; apply Subtype.ext; ext v; rw [←two_test i _ true,h,two_test]
lemma two_quiet : two (Marks V|>.quiet) = (Marks (V×Bool)).quiet:= by apply Subtype.ext;simp [two,Census.quiet]
lemma two_final : two (Stock.final V)=Stock.final (V×Bool):=by apply Subtype.ext; ext ⟨v,b⟩; simp [two, Stock.final]
lemma two_card (i:(Marks V).Mode) : (two i).val.card = i.val.card*2:=by simp [two]
lemma two_union (i j:(Marks V).Mode) (p:(Marks V).Mode)(hp:p.val=i.val ∪ j.val): (two p).val=(two i).val ∪ (two j).val:=by ext ⟨v,b⟩; simp [two,hp]
lemma two_dis (i j:(Marks V).Mode) : Disjoint (two i).val (two j).val ↔ Disjoint i.val j.val:=by
   simp only[Finset.disjoint_left]; constructor
   · intro h v hi hj; exact h ((two_test i v true).mpr hi) ((two_test j v true).mpr hj)
   rintro h ⟨v,b⟩ hi hj; exact h ((two_test i v b).mp hi) ((two_test j v b).mp hj)

-- linear map by coefficients into tagged monomials. no measure substitution assumption

def sealL (V:Type)[Fintype V][DecidableEq V]: Poly (Marks V) →ₗ[ℂ] Poly (Marks (V×Bool)) where
    toFun X:= ∑ i:(Marks V).Mode, Poly.send (two i) (X.part i)
    map_add' X Y:= by ext b; simp only [Poly.part_sum,Poly.part_send,Poly.part_plus,← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=> by split <;> simp
    map_smul' c X:=by ext b; change (∑ i:(Marks V).Mode, Poly.send (two i) ((c • X).part i)).part b = (c • (∑ i:(Marks V).Mode, Poly.send (two i) (X.part i))).part b; simp only [Poly.part_sum,Poly.part_send,Poly.part_smul,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by split <;> simp

lemma sealL_send (i:(Marks V).Mode)(a:ℂ): sealL V (Poly.send i a)=Poly.send (two i) a:=by
  ext k; change (∑ j:(Marks V).Mode,Poly.send (two j) ((Poly.send i a).part j)).part k=_
  rw [Poly.part_sum,Finset.sum_eq_single i]; simp; intro j _ h; simp [h]; simp

def duplicate (V:Type)[Fintype V][DecidableEq V] : Poly (Marks V) →ₐ[ℂ] Poly (Marks (V×Bool)) := by
    refine AlgHom.ofLinearMap (sealL V) ?_ ?_
    · change sealL V (Poly.send (Marks V|>.quiet) 1)=_
      rw [sealL_send,two_quiet]; rfl
    have hh(i j:(Marks V).Mode)(x y:ℂ): sealL V (Poly.send i x * Poly.send j y) = sealL V (Poly.send i x) * sealL V (Poly.send j y):=by
       rw [sealL_send,sealL_send]
       let z:(Marks V).Mode:= ⟨i.val ∪ j.val,mem_univ _⟩
       by_cases hp:Disjoint i.val j.val
       · have he:Poly.merges i j z:= ⟨hp,rfl⟩
         have hz:Poly.merges (two i) (two j) (two z):= ⟨two_dis ..|>.mpr hp,(two_union i j z rfl).symm⟩
         rw [Multi.send_prod he,Multi.send_prod hz,sealL_send]
       have hP: ¬∃ z',Poly.merges i j z':= fun ⟨_,h,_⟩=> hp h
       rw [Multi.send_noProd hP,Multi.send_noProd (show ¬∃ z',Poly.merges (two i) (two j) z' from fun ⟨_,h,_⟩=>hp (two_dis .. |>.mp h)),map_zero]
    intro x y
    rw [← Poly.studs x, ← Poly.studs y]; simp_rw [Finset.sum_mul,Finset.mul_sum,map_sum,hh,Finset.sum_mul,Finset.mul_sum]

lemma seal_send (i:(Marks V).Mode)(a:ℂ): duplicate V (Poly.send i a)=Poly.send (two i) a:=sealL_send ..

lemma seal_part (p: Poly (Marks V))(i:(Marks V).Mode): (duplicate V p).part (two i)=p.part i:=by
   change (∑ j:(Marks V).Mode,Poly.send (two j) (p.part j)).part (two i)=_
   have h (j:(Marks V).Mode):two i=two j ↔ i=j:= two_inj.eq_iff
   simp [Poly.part_sum,h]
lemma seal_miss (p:Poly (Marks V))(i:(Marks (V×Bool)).Mode)(h:∀ j:(Marks V).Mode,i≠two j): (duplicate V p).part i=0:=by
   change (∑ j:(Marks V).Mode,Poly.send (two j) (p.part j)).part _=_
   simp [Poly.part_sum,h]
lemma seal_pass (p:Poly (Marks V))(h:p.part (Marks V|>.quiet)=0): duplicate V (Poly.pass p) = Poly.pass (duplicate V p):=by
   apply Multi.pass_map _ _ h; rw [← two_quiet,seal_part,h]

end YM.Lodestar
