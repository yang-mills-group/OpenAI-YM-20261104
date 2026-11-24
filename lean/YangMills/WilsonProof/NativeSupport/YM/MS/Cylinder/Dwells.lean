import YM.MS.KoszulAllocate
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Cylinder formal analytic kernels

No bounded rank here; supports finite sets of position modes. Maps from here
 on arbitrary Fourier spaces can be defined by testing these finite sets. We also use
 the original coefficient space as at finite volume. Cylinder at `ℤ` sites makes precise
 prewrap stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder
open Function Set Finset Koszul
variable {R A B : Type*} [CommRing R] {p : Sector A} {q : Sector B} {F H u v:Raw A R}
local infixl:70 " ⋄ "=>product p

/-- Supports only words all of whose letters are from this (per step finite) set. -/
def Uses (s:Set A) (F: Raw A R) := ∀ l, ∀ i∈ l,i ∉ s → F l=0
namespace Uses
variable {s s':Set A}
lemma zero (s:Set A) : Uses s (0:Raw A R):=fun _ _ _ _=>rfl
lemma add (h:Uses s F) (g:Uses s H): Uses s (F+H):=fun l i hi h'=> by simp [h l i hi h',g l i hi h']
lemma sub (h:Uses s F) (g:Uses s H): Uses s (F-H):=fun l i hi h'=>by simp [h l i hi h',g l i hi h']
lemma smul (c:R)(h:Uses s F): Uses s (c • F):=fun l i hi h'=>by simp [h l i hi h']
lemma neg (h:Uses s F): Uses s (-F):=by simpa using smul (-1:R) h
lemma sign (h:Uses s F)(b:Bool): Uses s (sign p b F):=fun l i hi h' => by simp [h l i hi h']
lemma drop (j) (h:Uses s F) : Uses s (D j F):= fun l i hi hi' => h (j::l) i (List.mem_cons_of_mem _ hi) hi'
lemma off {i} (hi:i∉s) (h:Uses s F): D i F=0:=funext fun l=>h (i::l) i (by simp) hi
lemma entire (F:Raw A R): Uses Set.univ F:=fun _ _ _ h=> (h (Set.mem_univ _)).elim
lemma mono (h:Uses s F) (hs:s⊆s'): Uses s' F:=fun l i hi hx => h l i hi fun h=>hx (hs h)
lemma sum {f:B→Raw A R} {J:Finset B} (h:∀ i∈J, Uses s (f i)): Uses s (∑ i∈J,f i):= by
    intro l i hv hm; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun j hj=> h j hj l i hv hm
lemma pair (h:Uses s F)(g:Uses s H): Uses s (F ⋄ H):= by
    intro l i hi hv; rw [scattered,(scatter_congr _ l _ (fun _ _=> (0:R)) ?_)]; swap
    · intro l r hs; rcases List.mem_append.mp ((split_perm hs).mem_iff.mpr hi) with he|he
      · rw [h l i he hv,zero_mul]
      rw [g r i he hv,mul_zero]
    exact map_zero (allocate ..)
end Uses

def fits (s:Set A) : Submodule R (Raw A R) where
   carrier := Uses s
   zero_mem':= Uses.zero _
   add_mem' {_ _} h g:= Uses.add h g
   smul_mem' c _ hc:= Uses.smul c hc

lemma uses {s:Set A} : F∈fits s ↔ Uses s F := Iff.rfl

def Stack (A R : Type*) [CommRing R] : Submodule R (Raw A R) where
   carrier:= {F|∃ s:Finset A, Uses (s:Set A) F}
   zero_mem' := ⟨∅,Uses.zero _⟩
   add_mem' := by
      classical
      rintro x y ⟨s,hs⟩ ⟨t,ht⟩; refine ⟨s∪t,?_⟩
      rw [Finset.coe_union]; exact (hs.mono Set.subset_union_left).add (ht.mono Set.subset_union_right)
   smul_mem' := by rintro x F ⟨s,hs⟩; exact ⟨s,hs.smul x⟩
abbrev Cyl (A R : Type*) [CommRing R]:= ↥(Stack A R)
lemma fromCyl (f : Cyl A R) : ∃ s:Finset A,Uses (s:Set A) f.val:= f.property
lemma packed {s:Finset A} (h:Uses (s:Set A) F): F∈ Stack A R:=⟨s,h⟩
lemma encloses (f g:Cyl A R): ∃ s:Finset A, Uses (s:Set A) f.val ∧ Uses (s:Set A) g.val:= by
    classical
    obtain ⟨s,hs⟩:=fromCyl f; obtain ⟨u,hu⟩:=fromCyl g; exact ⟨s∪u, hs.mono (by simp), hu.mono (by simp)⟩
lemma all_in [Fintype A]: Stack A R=⊤ := top_unique (fun i _=> packed (s:=Finset.univ) (by simpa using Uses.entire i))
lemma all_f [Fintype A] (F:Raw A R): F∈ Stack A R:= by rw [all_in]; exact Set.mem_univ _
def region [Fintype A]: Cyl A R≃ₗ[R] Raw A R where
   toFun := (Stack A R).subtype
   invFun F:= ⟨F,all_f F⟩
   left_inv _:= rfl
   right_inv _:=rfl
   map_add' := by intros; rfl
   map_smul' := by intros; rfl

/-! Cylinder restriction linear operations. -/
def enter (x:A) : Cyl A R→ₗ[R] Cyl A R:= (((D x).comp (Stack A R).subtype).codRestrict (Stack A R) fun f=> by obtain ⟨s,hs⟩:= fromCyl f; exact packed (hs.drop x))
def twisted (p:Sector A) (c:Bool): Cyl A R→ₗ[R] Cyl A R:= (((sign p c).comp (Stack A R).subtype).codRestrict (Stack A R) fun f=> by obtain ⟨s,hs⟩:= fromCyl f; exact packed (hs.sign c))
def couple (p:Sector A): Cyl A R →ₗ[R] Cyl A R →ₗ[R] Cyl A R where
   toFun f:= ((product p f.val).comp (Stack A R).subtype).codRestrict (Stack A R) fun g=> by obtain ⟨s,hs,hg⟩:= encloses f g; exact packed (hs.pair hg)
   map_add' x y:= LinearMap.ext fun i=> Subtype.ext (add_times p ..)
   map_smul' x g:= LinearMap.ext fun i=> Subtype.ext (smul_times p ..)

lemma byone (f g:Cyl A R) (h0:f.val []=g.val []) (Hx:∀ i,enter i f=enter i g) : f=g:= Subtype.ext (ext_D h0 fun i=> congr_arg Subtype.val (Hx i))
@[simp] lemma enterp (x) (f:Cyl A R) : (enter x f).val = D x f.val:= rfl
@[simp] lemma twistp (x) (f:Cyl A R): (twisted p x f).val = sign p x f.val:= rfl
@[simp] lemma coupled (f g:Cyl A R): (couple p f g).val=product p f.val g.val:=rfl
lemma notEnter (f:Cyl A R) {s:Set A} (h:Uses s f.val) (x:A) (hx:x∉s) : enter x f=0:= Subtype.ext (h.off hx)
lemma couple_diff (f g:Cyl A R) (i:A) : enter i (couple p f g)= couple p (enter i f) g+couple p (twisted p (p i) f) (enter i g) := Subtype.ext (D_product ..)

lemma zero_stack : (0:Cyl A R).val=0:=rfl
lemma add_stack (f g:Cyl A R): (f+g).val=f.val+g.val:= rfl
lemma smul_stack (c:R)(f:Cyl A R): (c • f).val=c • f.val:= rfl
lemma sum_stack (s:Finset B)(f:B→Cyl A R): (∑ i∈s,f i).val=∑ i∈s,(f i).val:= map_sum (Stack A R).subtype ..
end YM.MS.Cylinder
