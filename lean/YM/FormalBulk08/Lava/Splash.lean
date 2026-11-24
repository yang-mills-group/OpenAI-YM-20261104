import YM.FormalBulk08.Lava.Walls

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb Function
open MvPolynomial
open scoped BigOperators Classical
variable {V : Type*} (r : ℕ)
lemma cards_mono (m : V→₀ℕ) (h : Finsupp.degree m=r) : ∃ v : chain V r,cards v=monomial m 1 := by
   induction r generalizing m with
   | zero=> rw [Finsupp.degree_eq_zero_iff] at h; exact ⟨default, by simp [cards,h]⟩
   | succ r ih=>
      have hv : ⇑m ≠ (0 : V→ℕ) := fun he=>by have e := DFunLike.ext _ (0:V→₀ℕ) (congr_fun he); rw [e,map_zero] at h; omega
      obtain ⟨a,ha⟩:=Function.ne_iff.mp hv
      have hi : Finsupp.single a 1 ≤ m := by
        intro j; by_cases e:j=a
        · subst j; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero ha
        simp [e]
      have hx : Finsupp.single a 1+(m-Finsupp.single a 1)=m := add_tsub_cancel_of_le hi
      rw [←hx,map_add,Finsupp.degree_single] at h;
      obtain ⟨v,he⟩:= ih (m-Finsupp.single a 1) (by omega); use Fin.cons a v; rw [cards_cons,he]; nth_rw 2 [←hx];rw [monomial_single_add,pow_one]

variable [Fintype V]
lemma facade_range (p : TypeR V) (h : IsHomogeneous p r) : ∃ T : Tile V r, Agate T ∧ facade r T=p := by
   have he:= (homogeneousComponent_eq_self h).symm
   let U := facade (V:=V) r
   suffices hh : p ∈ LinearMap.range U by
      obtain ⟨T,e⟩:=hh; exact ⟨sand T,agate_sand _, (sand_facade _ T).trans e⟩
   rw [he,homogeneousComponent_apply]; refine Submodule.sum_mem _ (fun i hi=> ?_)
   obtain ⟨v,hv⟩:=cards_mono r i (Finset.mem_filter.mp hi).2
   refine ⟨Pi.single v (coeff i p),?_⟩
   change facade _ _=_; simp [facade_eq,Pi.single_apply,hv,C_mul_monomial,apply_ite C,ite_mul]

-- canonical normalization
def marble (p : TypeR V) : Tile V r := Classical.choose (facade_range _ (homogeneousComponent r p) (homogeneousComponent_isHomogeneous ..))
lemma marble_agate (p : TypeR V) : Agate (marble r p) := (Classical.choose_spec (facade_range _ _ (homogeneousComponent_isHomogeneous ..))).1
lemma marble_grade (p : TypeR V) : facade _ (marble r p)=homogeneousComponent r p:= (Classical.choose_spec (facade_range _ _ (homogeneousComponent_isHomogeneous ..))).2
lemma marble_rec (T : Tile V r) (h : Agate T) : marble r (facade r T)=T:= facade_unique (marble_agate _ _) h (by rw [marble_grade,homogeneousComponent_eq_self (facade_grade _ _)])
lemma marble_add (p q : TypeR V) : marble r (p+q)=marble r p+marble r q := facade_unique (marble_agate _ _) ((marble_agate _ _).add (marble_agate _ _)) (by rw [map_add,marble_grade,marble_grade,marble_grade,map_add])
@[simp] lemma marble_zero : marble r (0 : TypeR V)=0 := by apply facade_unique (marble_agate _ _) (agate_zero _); rw [marble_grade,map_zero,map_zero]
def canyon : TypeR V →ₗ[ℝ] Tile V r where
   toFun := marble r
   map_add' := marble_add _
   map_smul' a p := facade_unique (marble_agate _ _) ((marble_agate _ _).smul a) (by rw [marble_grade,map_smul,map_smul,marble_grade];rfl)
lemma canyon_eq (p : TypeR V): canyon r p=marble r p:=rfl
lemma marble_eq_zero_iff (p : TypeR V) : marble r p=0 ↔ homogeneousComponent r p=0 := ⟨fun h=>by rw [←marble_grade,h,map_zero],fun h=> facade_unique (marble_agate _ _) (agate_zero _) (by rw [marble_grade,h,map_zero])⟩
end YM.FormalBulk08.Lava
