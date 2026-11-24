import YM.RG02.Marker.Connect
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion

/-!
# Separate predictor counting, source markers, and power counting

Here only **marker** and power variables, counted in two separate censuses.
No stochastic law in the product. Restrict also to a smaller census on either
factor, before assembly, without changing readings at the admitted modes.
Later we'll polarize powers by distinct copies; none of those copies mean
independent sampling of stochastic tags!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Marks
open Finset Marker Extra.Trajectories
open scoped BigOperators
variable {ι J : Type} [DecidableEq ι] [DecidableEq J]

/-- Keep all subsets. -/
def full (ι : Type) [DecidableEq ι] [Fintype ι] : Census ι where
  choices := univ
  blank := mem_univ _
  solo _ := mem_univ _
  down _ _ _ := mem_univ _

def together (R : Census ι) (S : Census J) : Census (ι ⊕ J) where
  choices := (R.choices ×ˢ S.choices).image fun p => p.1.disjSum p.2
  blank := mem_image.mpr ⟨(∅,∅),mem_product.mpr ⟨R.blank,S.blank⟩,rfl⟩
  solo a := by
    cases a with
    | inl i => exact mem_image.mpr ⟨({i},∅),mem_product.mpr ⟨R.solo i,S.blank⟩,rfl⟩
    | inr j => exact mem_image.mpr ⟨(∅,{j}),mem_product.mpr ⟨R.blank,S.solo j⟩,rfl⟩
  down hx z hz := by
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hx
    refine mem_image.mpr ⟨(z.toLeft,z.toRight),mem_product.mpr ?_, toLeft_disjSum_toRight⟩
    exact ⟨R.down (mem_product.mp hab).1 _ (subset_disjSum.mp hz).1,
      S.down (mem_product.mp hab).2 _ (subset_disjSum.mp hz).2⟩

namespace Pair
variable {R : Census ι} {S : Census J}

def mk (i : R.Mode) (j : S.Mode) : (together R S).Mode :=
  ⟨i.val.disjSum j.val, mem_image.mpr ⟨(i.val,j.val),mem_product.mpr ⟨i.property,j.property⟩,rfl⟩⟩

def fst (p : (together R S).Mode) : R.Mode := ⟨p.val.toLeft,by
  obtain ⟨⟨i,j⟩,hp,h⟩ := mem_image.mp p.property
  change i.disjSum j=p.val at h
  rw [← h,toLeft_disjSum]; exact (mem_product.mp hp).1⟩
def snd (p : (together R S).Mode) : S.Mode := ⟨p.val.toRight,by
  obtain ⟨⟨i,j⟩,hp,h⟩ := mem_image.mp p.property
  change i.disjSum j=p.val at h
  rw [← h,toRight_disjSum]; exact (mem_product.mp hp).2⟩

@[simp] lemma fst_mk (i : R.Mode) (j : S.Mode) : fst (mk i j)=i := Subtype.ext toLeft_disjSum
@[simp] lemma snd_mk (i : R.Mode) (j : S.Mode) : snd (mk i j)=j := Subtype.ext toRight_disjSum
@[simp] lemma mk_read (p : (together R S).Mode) : mk (fst p) (snd p) = p := Subtype.ext toLeft_disjSum_toRight
@[simp] lemma quiet : mk R.quiet S.quiet = (together R S).quiet := rfl
@[simp] lemma fst_quiet : fst (together R S).quiet = R.quiet := fst_mk R.quiet S.quiet
@[simp] lemma snd_quiet : snd (together R S).quiet = S.quiet := snd_mk R.quiet S.quiet

lemma mk_inj (i i' : R.Mode) (j j' : S.Mode) : mk i j = mk i' j' ↔ i=i' ∧ j=j' := by
  constructor
  · intro h; exact ⟨by simpa only [fst_mk] using congr_arg fst h,by simpa only [snd_mk] using congr_arg snd h⟩
  rintro ⟨rfl,rfl⟩; rfl

def iso : R.Mode × S.Mode ≃ (together R S).Mode :=
  ⟨fun p => mk p.1 p.2, fun p => (fst p,snd p),fun ⟨i,j⟩ => Prod.ext (fst_mk i j) (snd_mk i j),mk_read⟩

lemma merges (i j k : R.Mode) (a b c : S.Mode) :
    Poly.merges (mk i a) (mk j b) (mk k c) ↔ Poly.merges i j k ∧ Poly.merges a b c := by
  unfold Poly.merges mk; dsimp only
  have hv : (i.val.disjSum a.val) ∪ (j.val.disjSum b.val) = (i.val ∪ j.val).disjSum (a.val ∪ b.val) := by
    ext p; cases p <;> simp
  rw [hv,disjSum_inj]
  simp only [Finset.disjoint_left]
  constructor
  · rintro ⟨h,h₁,h₂⟩
    exact ⟨⟨fun x ha hb => h (by simpa using ha : Sum.inl x ∈ _) (by simpa using hb),h₁⟩,
           ⟨fun x ha hb => h (by simpa using ha : Sum.inr x ∈ _) (by simpa using hb),h₂⟩⟩
  rintro ⟨⟨h,hh⟩,⟨g,hg⟩⟩
  refine ⟨fun v => ?_,hh,hg⟩
  cases v with
  | inl i => intro hv ht; exact h (by simpa using hv) (by simpa using ht)
  | inr i => intro hv ht; exact g (by simpa using hv) (by simpa using ht)

/-- Tensor is the product of the two separately embedded elements. -/
def tensor (x : Poly R) (y : Poly S) : Poly (together R S) :=
  Poly.inject fun p => x.part (fst p)*y.part (snd p)
@[simp] lemma tensor_mk (x : Poly R) (y : Poly S) (i j) :
    (tensor x y).part (mk i j)=x.part i*y.part j := by simp [tensor,Poly.part,Poly.inject]

lemma tensor_mul (w x : Poly R) (y z : Poly S) : tensor (w*x) (y*z) = tensor w y*tensor x z := by
  ext t
  obtain ⟨⟨i,j⟩,rfl⟩ := iso.surjective t
  change (tensor (w*x) _).part (mk i j) = _
  rw [Poly.part_mul]
  -- reindex RHS
  rw [← Equiv.sum_comp iso]
  rw [Fintype.sum_prod_type]
  conv_rhs => arg 2; ext; arg 2; ext; rw [← Equiv.sum_comp iso, Fintype.sum_prod_type]
  simp only [iso,Equiv.coe_fn_mk, tensor_mk, merges]
  rw [Poly.part_mul,Poly.part_mul,sum_mul]; apply sum_congr rfl; intro p _
  rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]; rw [sum_comm (f:=fun (q : R.Mode) a => _)]
  apply sum_congr rfl; intro l _; apply sum_congr rfl; intro q _; apply sum_congr rfl; intro m _
  by_cases h : Poly.merges p q i <;> by_cases hv : Poly.merges l m j <;> simp [h,hv]
  ring

@[simp] lemma tensor_unit : tensor (1 : Poly R) (1 : Poly S)=1 := by
  ext t
  rw [← mk_read t, tensor_mk, Poly.one_part, Poly.one_part, Poly.one_part, ← quiet]
  simp only [mk_inj]
  aesop

def embedL (S : Census J) : Poly R →ₐ[ℂ] Poly (together R S) := AlgHom.ofLinearMap
  { toFun x := tensor x 1
    map_add' x y := by
      ext t
      rw [← mk_read t,Poly.part_plus,tensor_mk,tensor_mk,tensor_mk,Poly.part_plus,add_mul]
    map_smul' a x := by
      ext t
      rw [← mk_read t,Poly.part_smul, tensor_mk, tensor_mk, Poly.part_smul,mul_assoc]; rfl }
  tensor_unit (fun x y => (by simpa only [LinearMap.coe_mk, AddHom.coe_mk,one_mul] using tensor_mul (S:=S) x y 1 1))

def embedR (R : Census ι) : Poly S →ₐ[ℂ] Poly (together R S) := AlgHom.ofLinearMap
  { toFun y := tensor 1 y
    map_add' x y := by
      ext t
      rw [← mk_read t,Poly.part_plus,tensor_mk,tensor_mk,tensor_mk,Poly.part_plus,mul_add]
    map_smul' a y := by
      ext t
      rw [← mk_read t, Poly.part_smul,tensor_mk,tensor_mk,Poly.part_smul,RingHom.id_apply]; ac_rfl }
  tensor_unit (fun x y => (by simpa only [LinearMap.coe_mk, AddHom.coe_mk,one_mul] using tensor_mul (R:=R) 1 1 x y))

lemma tensor_eq (x : Poly R) (y : Poly S) : tensor x y = (embedL S x)*(embedR R y) := by
  change _=tensor x 1*tensor 1 y
  rw [← tensor_mul,mul_one,one_mul]

lemma part_product (x : Poly R) (y : Poly S) (t : (together R S).Mode) :
    (embedL S x * embedR R y).part t=x.part (fst t)*y.part (snd t) := by
  rw [← tensor_eq]; rfl

end Pair
end YM.RG02.Marks
