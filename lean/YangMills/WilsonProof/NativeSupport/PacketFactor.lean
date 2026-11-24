import YangMills.WilsonProof.NativeSupport.PacketPrice

/-! The within-word tables required by `word_price` are the actual marginals
of the full planted tape, even if a word has widely separated slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Finset Marker Extra.Trajectories
open scoped Classical BigOperators
variable {V H ι : Type*} [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H]
local notation "Π₀" => Poly (Stock.census V)

private lemma unit_part (S : Finset V) : (1 : Π₀).part (tag S) = if S=∅ then 1 else 0 := by
  rw [Poly.one_part]
  congr 1
  exact propext Subtype.ext_iff

private lemma add_mark (P : Π₀) (D S : Finset V) (c : ℂ) :
    (P*(1+Poly.send (tag D) c)).part (tag S) = P.part (tag S) +
      if D⊆S then P.part (tag (S\D))*c else 0 := by
  rw [mul_add, mul_one, Poly.part_plus, shift_part]

omit [Fintype H] [DecidableEq V] in
private lemma fitted {g : V → H} {h : H} {D : Finset V}
    (home : D ⊆ fibre g h) {j : H} (ne : j≠h) : Disjoint D (fibre g j) := by
  apply disjoint_left.mpr
  intro x hx hw
  have ha := (mem_filter.mp (home hx)).2
  have hb := (mem_filter.mp hw).2
  exact ne (hb.symm.trans ha)

private def Table (g : V → H) (P : Π₀) :=
  ∀ U : Finset V, P.part (tag U) = ∏ j, P.part (tag (U∩fibre g j))

private lemma table_one (g : V → H) : Table g 1 := by
  intro U
  simp_rw [unit_part]
  by_cases hu : U=∅
  · simp [hu]
  rw [if_neg hu]
  obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hu
  exact (prod_eq_zero (mem_univ (g x)) (if_neg
    (show U∩fibre g (g x)≠∅ from nonempty_iff_ne_empty.mp ⟨x,mem_inter.mpr ⟨hx,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩⟩))).symm

private lemma table_factor (g : V → H) (P : Π₀) (hp : Table g P) (D : Finset V)
    (c : ℂ) (h : H) (hd : D.Nonempty) (home : D⊆fibre g h) : Table g (P*(1+Poly.send (tag D) c)) := by
  intro U
  simp_rw [add_mark]
  by_cases hu : D⊆U
  · have hinc : D⊆U∩fibre g h := subset_inter hu home
    have other (j : H) (hj : j≠h) : ¬D⊆U∩fibre g j := by
      obtain ⟨x,hx⟩ := hd
      exact fun hh => disjoint_left.mp (fitted home hj) hx (mem_inter.mp (hh hx)).2
    have diff (j : H) (hj : j≠h) : (U\D)∩fibre g j = U∩fibre g j := by
      ext x
      simp only [mem_inter,mem_sdiff]
      constructor
      · tauto
      · rintro ⟨a,b⟩
        exact ⟨⟨a,fun k => disjoint_left.mp (fitted home hj) k b⟩,b⟩
    have mid : (U\D)∩fibre g h=(U∩fibre g h)\D := by ext x; simp only [mem_inter,mem_sdiff]; tauto
    rw [if_pos hu, hp U, hp (U\D), ← prod_erase_mul _ _ (mem_univ h),
      ← prod_erase_mul _ (fun j => P.part (tag ((U\D)∩fibre g j))) (mem_univ h), mid]
    rw [← prod_erase_mul _ (fun j=>P.part (tag (U∩fibre g j)) + _) (mem_univ h), if_pos hinc]
    let z := ∏ j ∈ univ.erase h, P.part (tag (U∩fibre g j))
    have m₁ : (∏ j ∈ univ.erase h, P.part (tag ((U\D)∩fibre g j))) = z := by
      apply prod_congr rfl; intro j hj; rw [diff _ (mem_erase.mp hj).1]
    have m₂ : (∏ j ∈ univ.erase h, (P.part (tag (U∩fibre g j)) +
      if D⊆U∩fibre g j then P.part (tag ((U∩fibre g j)\D))*c else 0))=z := by
      apply prod_congr rfl; intro j hj; rw [if_neg (other _ (mem_erase.mp hj).1),add_zero]
    rw [m₁,m₂]
    change z*_+z*_*c = z*(_+_*c)
    ring
  · rw [if_neg hu,add_zero,hp U]
    apply prod_congr rfl
    intro j _
    rw [if_neg (fun h => hu (h.trans inter_subset_left)), add_zero]

private lemma outside (P : Π₀) (K : Finset ι) (D : ι → Finset V) (c : ι → ℂ) (U : Finset V)
    (notin : ∀ i ∈ K, ¬D i⊆U) :
    (P*∏ i ∈ K, (1+Poly.send (tag (D i)) (c i))).part (tag U) = P.part (tag U) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | insert i K hi ih =>
    rw [prod_insert hi, mul_left_comm P, mul_comm _ (P*_)]
    rw [add_mark, if_neg (notin _ (mem_insert_self ..)), add_zero]
    exact ih (fun j hj => notin _ (mem_insert_of_mem hj))

private lemma table_product (g : V → H) (I : Finset ι) (D : ι → Finset V) (c : ι → ℂ)
    (internal : ∀ i ∈ I, (D i).Nonempty ∧ ∃ h, D i⊆fibre g h) :
    Table g (∏ i ∈ I, (1+Poly.send (tag (D i)) (c i))) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using table_one g
  | insert i I hi ih =>
    rw [prod_insert hi,mul_comm]
    obtain ⟨he,h,hD⟩ := internal i (mem_insert_self ..)
    exact table_factor g _ (ih (fun j hj => internal _ (mem_insert_of_mem hj))) _ _ h he hD

/-- Independent evaluation of the within-fibre log terms gives precisely the
original submoments on each fibre. The full tape is recovered by including the
cross terms. -/
theorem factor_word_price (g : V → H) (I K : Finset ι) (D : ι → Finset V) (c : ι → ℂ)
    (internal : ∀ i ∈ I, (D i).Nonempty ∧ ∃ h, D i⊆fibre g h)
    (cross : ∀ i ∈ K, ∀ h, ¬D i⊆fibre g h) (P : Π₀)
    (tape : P=(∏ i ∈ I, (1+Poly.send (tag (D i)) (c i)))*(∏ i ∈ K, (1+Poly.send (tag (D i)) (c i))))
    (quiet : P.part (tag ∅)=1) (mom : ∀ U, ‖P.part (tag U)‖ ≤ 1)
    {w s : ℝ} (full : ∀ h, P.part (tag (fibre g h))=(w:ℂ))
    (hw : |w| ≤ 1) (hs : |s| ≤ 1/4) :
    ‖read g (s:ℂ) P‖ ≤ Real.exp (∑ i∈K, ‖c i‖)*(1+s*w)^Fintype.card H := by
  classical
  let Q := ∏ i ∈ I, (1+Poly.send (tag (D i)) (c i))
  have tbl : Table g Q := table_product g I D c internal
  have same (h : H) (U : Finset V) : Q.part (tag (U∩fibre g h)) = P.part (tag (U∩fibre g h)) := by
    rw [tape]
    exact (outside Q K D c _ fun i hi e => cross _ hi h (e.trans inter_subset_right)).symm
  let M (h : H) (U : Finset V) := P.part (tag (U∩fibre g h))
  have tab (U : Finset V) : Q.part (tag U) = ∏ h, M h (U∩fibre g h) := by
    rw [tbl U]
    apply prod_congr rfl
    intro h _
    simpa [M,inter_assoc] using same h U
  rw [tape]
  apply cross_price
  exact word_price g s Q M (fun h=>by simpa [M] using quiet) tab (fun _ _ => mom _)
    (fun h=>by simpa [M] using full h) hw hs

end YM.Integration.InletSusceptibility.Packet
