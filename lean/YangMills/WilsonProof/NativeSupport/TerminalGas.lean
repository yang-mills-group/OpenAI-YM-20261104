import YangMills.WilsonProof.NativeSupport.PacketPrice

/-! Deleting one marker in the actual square-free exponential. Partial
evaluation sums over the permitted thermal and physical subsets. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.TerminalGas
open Finset Marker Extra.Trajectories Packet
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Π₀" => Poly (Stock.census V)

def sliceZ (A : Finset V) (P : Π₀) : ℂ := ∑ S ∈ A.powerset, P.part (tag S)

private theorem shift (A T : Finset V) (P : Π₀) (c : ℂ) :
    sliceZ A (P*Poly.send (tag T) c) =
      if T⊆A then c*sliceZ (A\T) P else 0 := by
  by_cases h : T⊆A
  · rw [if_pos h]
    unfold sliceZ
    simp_rw [shift_part]
    rw [← sum_filter, mul_sum]
    apply sum_bij' (fun S _ => S\T) (fun S _ => S∪T)
    · intro S hS
      exact mem_powerset.mpr fun _ hx => mem_sdiff.mpr
        ⟨(mem_powerset.mp (mem_filter.mp hS).1) (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩
    · intro S hS
      exact mem_filter.mpr ⟨mem_powerset.mpr (union_subset ((mem_powerset.mp hS).trans sdiff_subset) h),subset_union_right⟩
    · intro S hS; exact sdiff_union_of_subset (mem_filter.mp hS).2
    · intro S hS
      have hs := mem_powerset.mp hS
      ext x; simp only [mem_sdiff,mem_union]
      constructor
      · tauto
      · intro hx; exact ⟨Or.inl hx,(mem_sdiff.mp (hs hx)).2⟩
    · intro S _; exact mul_comm ..
  · rw [if_neg h]
    unfold sliceZ
    apply sum_eq_zero
    intro S hS
    rw [shift_part,if_neg (fun hh => h (hh.trans (mem_powerset.mp hS)))]

def factors (F : Finset (Finset V)) (c : Finset V → ℂ) : Π₀ :=
  ∏ T ∈ F, (1+Poly.send (tag T) (c T))

private lemma increment (F : Finset (Finset V)) (c : Finset V → ℂ) (A T : Finset V) (ht : T∉F) :
    sliceZ A (factors (insert T F) c) = sliceZ A (factors F c) +
      if T⊆A then c T * sliceZ (A\T) (factors F c) else 0 := by
  rw [factors,prod_insert ht,mul_comm,mul_add,mul_one]
  change sliceZ A (factors F c+factors F c*Poly.send (tag T) (c T)) = _
  rw [show sliceZ A (factors F c+factors F c*Poly.send (tag T) (c T)) =
      sliceZ A (factors F c)+sliceZ A (factors F c*Poly.send (tag T) (c T)) by
    simp only [sliceZ,Poly.part_plus,sum_add_distrib], shift]

private lemma trim (F : Finset (Finset V)) (c : Finset V → ℂ) (A : Finset V) (x : V) (hx : x∉A) :
    sliceZ A (factors F c) = sliceZ A (factors (F.filter fun T => x∉T) c) := by
  induction F using Finset.induction_on generalizing A with
  | empty => simp
  | @insert T F ht ih =>
    by_cases h : x∈T
    · rw [filter_insert,if_neg (not_not.mpr h), increment _ _ _ _ ht,if_neg (fun H => hx (H h)),add_zero,ih A hx]
    · rw [filter_insert,if_pos h,increment _ _ _ _ ht,
        increment _ _ _ _ (fun H => ht (mem_filter.mp H).1), ih A hx]
      split
      · rw [ih (A\T) (fun H => hx (mem_sdiff.mp H).1)]
      · rfl

private lemma delete_unused (F : Finset (Finset V)) (c : Finset V → ℂ) (A : Finset V) (x : V)
    (none : ∀ T∈F, x∉T) :
    sliceZ A (factors F c) = sliceZ (A.erase x) (factors F c) := by
  induction F using Finset.induction_on generalizing A with
  | empty =>
    simp only [factors, prod_empty, sliceZ, Poly.one_part]
    have z (S : Finset V) : tag S = (Stock.census V).quiet ↔ S=∅ := Subtype.ext_iff
    simp [z]
  | @insert T F ht ih =>
    have nf : ∀ D∈F, x∉D := fun D hD => none D (mem_insert_of_mem hD)
    have nx := none T (mem_insert_self ..)
    have eq : T⊆A.erase x ↔ T⊆A := by
      constructor
      · exact fun h => h.trans (erase_subset ..)
      · intro h y hy
        exact mem_erase.mpr ⟨fun e => nx (e ▸ hy),h hy⟩
    rw [increment _ _ _ _ ht,increment _ _ _ _ ht, ih A nf]
    by_cases h : T⊆A
    · rw [if_pos h,if_pos (eq.mpr h),ih (A\T) nf]
      have same : (A\T).erase x=A.erase x\T := by
        ext y; simp only [mem_erase,mem_sdiff]; tauto
      rw [same]
    · rw [if_neg h,if_neg (mt eq.mp h)]

private lemma touch (F D : Finset (Finset V)) (c : Finset V → ℂ) (A : Finset V)
    (x : V) (sep : Disjoint F D) (all : ∀ T∈D, x∈T) :
    sliceZ A (factors (F∪D) c) = sliceZ A (factors F c) +
      ∑ T ∈ D, if T⊆A then c T * sliceZ (A\T) (factors F c) else 0 := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert T D ht ih =>
    have hd : Disjoint F D := sep.mono_right (subset_insert ..)
    have hT : T∉F := fun h => disjoint_left.mp sep h (mem_insert_self ..)
    have live := all T (mem_insert_self ..)
    have sub : ∀ t∈D, x∈t := fun t h => all t (mem_insert_of_mem h)
    rw [union_insert,increment _ _ _ _ (notMem_union.mpr ⟨hT,ht⟩),ih hd sub,sum_insert ht]
    by_cases h : T⊆A
    · simp only [if_pos h]
      have na : x∉A\T := fun hh => (mem_sdiff.mp hh).2 live
      have rm : (F∪D).filter (fun S => x∉S)=F.filter (fun S => x∉S) := by
        ext S; simp only [mem_filter,mem_union]
        constructor
        · rintro ⟨hF|hD,nx⟩
          · exact ⟨hF,nx⟩
          · exact False.elim (nx (sub _ hD))
        · rintro ⟨hF,nx⟩; exact ⟨Or.inl hF,nx⟩
      rw [trim (F∪D) c (A\T) x na,rm,← trim F c (A\T) x na]
      ring
    · simp only [if_neg h]
      ring

theorem native_factors (H : Π₀) (quiet : H.part (Stock.census V).quiet=0) :
    Poly.pass H = factors (univ.filter fun T : Finset V => T.Nonempty) (fun T => H.part (tag T)) := by
  let F := univ.filter fun T : Finset V => T.Nonempty
  have parts : ∑ T ∈ F, Poly.send (tag T) (H.part (tag T)) = H := by
    ext j
    rw [Poly.part_sum]
    by_cases hj : j.val.Nonempty
    · rw [sum_eq_single j.val]
      · simp [Poly.part_send]
      · intro S _ hs
        rw [Poly.part_send,if_neg (fun e => hs (congrArg Subtype.val e).symm)]
      · intro n; exact False.elim (n (mem_filter.mpr ⟨mem_univ _,hj⟩))
    · have hz : j=(Stock.census V).quiet := Subtype.ext (not_nonempty_iff_eq_empty.mp hj)
      rw [hz,quiet]
      apply sum_eq_zero
      intro S hS
      rw [Poly.part_send,if_neg (fun e => (mem_filter.mp hS).2.ne_empty (congrArg Subtype.val e).symm)]
  exact (congrArg Poly.pass parts.symm).trans (pass_sum F tag (fun T hT => (mem_filter.mp hT).2) _)

private theorem deletion_split (F D E : Finset (Finset V)) (c : Finset V → ℂ) (A : Finset V) (x : V)
    (join : D∪E=F) (sep : Disjoint D E) (old : ∀ T∈D,x∉T) (fresh : ∀ T∈E,x∈T)
    (trimmed : ∀ B : Finset V,x∉B → sliceZ B (factors D c)=sliceZ B (factors F c)) :
    sliceZ A (factors F c)=sliceZ (A.erase x) (factors F c)+
      ∑ T∈E,if T⊆A then c T*sliceZ (A\T) (factors F c) else 0 := by
  have original:=congrArg (fun J=>sliceZ A (factors J c)) join
  refine original.symm.trans ((touch D E c A x sep fresh).trans ?_)
  apply congrArg₂ (·+·)
  · exact (delete_unused D c A x old).trans (trimmed _ (notMem_erase x A))
  · apply sum_congr rfl
    intro T ht
    by_cases sub:T⊆A
    · simp only [if_pos sub]
      exact congrArg (fun z=>c T*z) (trimmed _ (fun h=>(mem_sdiff.mp h).2 (fresh T ht)))
    · simp only [if_neg sub]

private theorem deletion_factors (c : Finset V → ℂ) (A : Finset V) (x : V) :
    let F := (univ : Finset (Finset V)).filter fun T => T.Nonempty
    sliceZ A (factors F c) = sliceZ (A.erase x) (factors F c) +
      ∑ T ∈ (univ : Finset (Finset V)).filter (fun T => x∈T),
        if T⊆A then c T*sliceZ (A\T) (factors F c) else 0 := by
  intro F
  let D := F.filter fun T => x∉T
  let E := (univ : Finset (Finset V)).filter fun T => x∈T
  have join : D∪E=F := by
    ext T; simp only [D,E,F,mem_union,mem_filter,mem_univ,true_and]
    exact ⟨fun h => h.elim And.left (fun ht => ⟨x,ht⟩),fun ht => (em (x∈T)).elim Or.inr (fun hn=>Or.inl ⟨ht,hn⟩)⟩
  have sep : Disjoint D E := disjoint_left.mpr fun _ h₁ h₂ => (mem_filter.mp h₁).2 (mem_filter.mp h₂).2
  exact deletion_split F D E c A x join sep (fun _ h=>(mem_filter.mp h).2) (fun _ h=>(mem_filter.mp h).2)
    (fun B hb=>(trim F c B x hb).symm)

theorem deletion (H : Π₀) (quiet : H.part (Stock.census V).quiet=0) (A : Finset V) (x : V) :
    sliceZ A (Poly.pass H) = sliceZ (A.erase x) (Poly.pass H) +
      ∑ T ∈ (univ : Finset (Finset V)).filter (fun T => x∈T),
        if T⊆A then H.part (tag T)*sliceZ (A\T) (Poly.pass H) else 0 := by
  simpa only [native_factors H quiet] using deletion_factors (fun T=>H.part (tag T)) A x

end YM.Integration.InletSusceptibility.TerminalGas
