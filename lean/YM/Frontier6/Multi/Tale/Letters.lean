import YM.Frontier6.Multi.Tale.Word

/-! Facing projections; choose once full α and hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Tale
open Function Set Finset Filter Spec
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {I J : Type*}[Fintype I][Fintype J]
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(K: Final C F S)
variable (x:E4) (d:ℕ)(t:S.Tag)(A:S.Field d)

lemma combine_letter (v:I→ S.Field d) (a:I→ℂ): Congr K (∑ i:I,a i • letter S x ⟨d,v i⟩) (letter S x ⟨d,∑ i,a i • v i⟩):=by
   intro y α; rw [sum_mul,map_sum]; simp_rw [smul_mul_assoc,map_smul, ← reads K,map_sum,map_smul]
lemma multi_up {e:ℕ}(h:e ≤ d)(u:I→ S.Field e)(a:I→ℂ): Congr K (∑ i:I,a i • letter S x ⟨e,u i⟩) (letter S x ⟨d,higher K h (∑ i,a i • u i)⟩) := (combine_letter K x e u a).trans K (letter_cap K x e _ h)
lemma Congr.total (p q:I→ Spelling S)(h:∀ i,Congr K (p i) (q i)): Congr K (∑ i,p i) (∑ i,q i):=by
   intro x α; rw [sum_mul,map_sum,sum_mul,map_sum]; exact sum_congr rfl fun i _=> h i x α

set_option quotPrecheck false
abbrev Slugs := Fin (Module.finrank ℂ (Grade K d))
abbrev marker := Module.finBasis ℂ (Grade K d)
def face : S.Field d→ₗ[ℂ] (Grade K d):= LinearMap.rangeRestrict (weight K d).toLinearMap

def suit (x:E4) (w:ℕ): S.Field w→ₗ[ℂ] Spelling S:= ∑ i:Slugs K w, (((marker K w).coord i).comp (face K w)).smulRight (letter S x ⟨w,(marker K w i).val⟩)
local notation "I'"=> Slugs K d
lemma suit_reads : Congr K (suit K x d A) (letter S x ⟨d,weight K d A⟩):=by
    let v(i:I'):= marker K d i; let p:=face K d A; let a(i:I'):= (marker K d).coord i p
    have he:∑ i,a i • (v i).val=weight K d A:=by
       change ∑ i:I', a i • ((Grade K d).subtype (v i)) = (Grade K d).subtype (face K d A); simp only [← map_smul,← map_sum]; rw [(show ∑ i,a i • v i=p from (marker K d).sum_repr p)]
    unfold suit; rw [LinearMap.sum_apply]; rw [←he]; exact combine_letter K x d (fun i:I'=> (v i).val) a -- might implicit
lemma suit_eq (x:E4): suit K x d A= ∑ i:Slugs K d,(marker K d).coord i (face K d A) • letter S x ⟨d,(marker K d i).val⟩:= LinearMap.sum_apply ..

def reach (K:Final C F S)(d:ℕ)(i:Fin (d+1)): S.Field d→L[ℂ] S.Field i:= projectBelow K (show (i:ℕ) ≤ d by have:=i.isLt; omega)
def rankMember (K:Final C F S)(d:ℕ)(i:Fin (d+1)): S.Field i→L[ℂ] S.Field d := higher K (show (i:ℕ) ≤ d by have:=i.isLt; omega)
def deck : S.Field d →ₗ[ℂ] Spelling S:= ∑ i:Fin (d+1), (suit K x i).comp ((reach K d i).toLinearMap)
lemma deck_eq : deck K x d A=∑ i:Fin (d+1),suit K x i (reach K d i A):= LinearMap.sum_apply ..
lemma deck_at : Congr K (deck K x d A) (letter S x ⟨d,A⟩):=by
    rw [deck_eq]; let V(i:Fin (d+1)):= weight K i (reach K d i A); let f i:= rankMember K d i (V i)
    refine (Congr.total _ _ (fun i:Fin (d+1)=>letter S x ⟨d,f i⟩) (fun i=> (suit_reads K x (i:ℕ) _).trans K (letter_cap K x _ (V i) (by exact Nat.lt_add_one_iff.mp i.isLt)))).trans K ?_
    have he:= combine_letter K x d f (fun _=>1); simp only [one_smul] at he; rw [show ∑ i,f i=A from weights_span K _] at he; exact he
lemma face_appears (x:E4): suit K x d (weight K d A)=suit K x d A:=by rw [suit_eq,suit_eq]; rw [show face K d (weight K d A)=face K d A from Subtype.ext (weight_idem K _)]
lemma suit_appears {y d:ℕ}(i:Fin (d+1))(e:y< d)(he:i.val<y)(B:S.Field y): suit K x i (reach K d i (higher K e.le (weight K y B)))=0:=by rw [←face_appears, show reach K d i (higher K e.le _)= 0 from (projects_arrive K he.le e.le _).trans (projects_pure K he _),map_zero,map_zero]

lemma figurative (d:I→ℕ)(f: (i:I)→ J → S.Field (d i)) (g:I→J→ℂ)(x:I→ E4) : Congr K
    (∏ i:I, ∑ j:J,g i j • letter S (x i) ⟨d i,f i j⟩) (assembly S x (fun i=>⟨d i,∑ j,g i j • f i j⟩)):= by apply Congr.product; intro i _; exact combine_letter K (x i) (d i) (f i) (g i)

-- factored expansion on variant families of branches, moving cuts etc.
lemma muls {R0:Type*}[Fintype R0][_d:DecidableEq R0]{J:R0→Type*}[_i:∀ i,Fintype (J i)](A:∀ i,J i→Spelling S) (f:∀ i,J i→ℂ) : ∏ i:R0, ∑ j:J i, f i j • A i j=∑ s:∀ i:R0,J i, (∏ i:R0,f i (s i)) • ∏ i:R0, A i (s i):=by
    rw [Fintype.prod_sum]; refine sum_congr rfl fun i _=>?_; exact Finset.prod_smul .. -- test
end YM.Frontier6.Tale
