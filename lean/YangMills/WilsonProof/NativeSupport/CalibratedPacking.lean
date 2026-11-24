import YM.Corona.Fit

/-! Packing separated terminal anchors in the actual native connected cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Finset YM.Lattice YM.Lattice.Corona
open scoped Classical BigOperators

private lemma same_bin {x y L : ℕ} (pos : 0 < L) (eq : x / L = y / L) :
    y - x < L := by
  have a := Nat.mod_add_div x L
  have b := Nat.mod_add_div y L
  rw [eq] at a
  have := Nat.mod_lt y pos
  omega

/-- Every separated word represented in a support consumes at least H
native cover balls, as soon as two words are represented. -/
theorem separated_cover {n : Side} (M H : ℕ) (hH : 0 < H) (X A : Support n)
    (inside : A ⊆ X) (many : 2 ≤ A.card)
    (far : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      2*M+4*(2*M+1)*H < separation x y) :
    A.card * H ≤ coverNumber M X := by
  classical
  let L := 4*(2*M+1)*H
  have hp : 0 < L := by dsimp [L]; positivity
  obtain ⟨D, cover, hD⟩ := coverNumber_realized M X
  obtain ⟨N,hN,R,walk,visits⟩ := ring_path _ (halo_ship _ cover.2)
  have incidence (x : A) : ∃ j ≤ N, separation (R j) x.val ≤ M := by
    obtain ⟨c,hc,close⟩ := halo_spec.mp (cover.1 (inside x.property))
    obtain ⟨j,hj,eq⟩ := visits c hc
    exact ⟨j,hj,eq ▸ close⟩
  choose τ τle near using incidence
  let bin (x : A) : Fin (N/L+1) :=
    ⟨τ x/L, Nat.lt_succ_of_le (Nat.div_le_div_right (τle x))⟩
  have inject : Function.Injective bin := by
    intro x y he
    by_contra neq
    have gap := far x x.property y y.property (fun h => neq (Subtype.ext h))
    have eq : τ x/L = τ y/L := congrArg Fin.val he
    have dist : separation (R (τ x)) (R (τ y)) < L := by
      rcases le_total (τ x) (τ y) with h | h
      · exact (path_span walk _ _ h (τle y)).trans_lt (same_bin hp eq)
      · rw [separation_comm]
        exact (path_span walk _ _ h (τle x)).trans_lt (same_bin hp eq.symm)
    have nx := near x
    rw [separation_comm] at nx
    have ny := near y
    have h₁ := separation_triangle x.val (R (τ x)) y.val
    have h₂ := separation_triangle (R (τ x)) (R (τ y)) y.val
    change 2*M+L < _ at gap
    omega
  have card : A.card ≤ N/L+1 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective _ inject
  have half : A.card ≤ 2*(N/L) := by omega
  have mul := Nat.mul_le_mul_right L half
  have small := Nat.div_mul_le_self N L
  have pack : A.card * H * (4*(2*M+1)) ≤ D.card * (4*(2*M+1)) := by
    calc
      _ = A.card * L := by dsimp [L]; ring
      _ ≤ 2 * ((N/L)*L) := mul.trans_eq (by ring)
      _ ≤ 2 * N := Nat.mul_le_mul_left 2 small
      _ ≤ 2 * (D.card * ((M+M+1)+(M+M+1))) := Nat.mul_le_mul_left 2 hN
      _ = D.card * (4*(2*M+1)) := by ring
  rw [← hD]
  exact Nat.le_of_mul_le_mul_right pack (by positivity)

/-- Greedy selection with a lower density in an arbitrary finite torus.
The input near set includes the translation itself. -/
theorem sparse_subset {α : Type*} [DecidableEq α] (near : α → Finset α)
    (refl : ∀ i, i ∈ near i) (sym : ∀ i j, i ∈ near j → j ∈ near i)
    (χ : ℕ) (degree : ∀ i, (near i).card ≤ χ) (S : Finset α) :
    ∃ I ⊆ S, (∀ i ∈ I, ∀ j ∈ I, i ≠ j → j ∉ near i) ∧ S.card ≤ I.card*χ := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨j,hj⟩
    · exact ⟨∅,Subset.rfl,by simp,by simp⟩
    let T := S \ near j
    have sub : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun eq =>
      (mem_sdiff.mp (eq ▸ hj : j ∈ T)).2 (refl j)⟩
    obtain ⟨I,hI, sep, hcard⟩ := ih T sub
    have nj : j ∉ I := fun h => (mem_sdiff.mp (hI h)).2 (refl j)
    refine ⟨insert j I, insert_subset hj (hI.trans sdiff_subset), ?_, ?_⟩
    · intro x hx y hy ne close
      rcases mem_insert.mp hx with h | hxi
      · subst x
        have hyi := (mem_insert.mp hy).resolve_left ne.symm
        exact (mem_sdiff.mp (hI hyi)).2 close
      · rcases mem_insert.mp hy with h | hyi
        · subst y
          exact (mem_sdiff.mp (hI hxi)).2 (sym j x close)
        · exact sep x hxi y hyi ne close
    · have cut := card_sdiff_add_card_inter S (near j)
      have rest := Finset.card_le_card (inter_subset_right : S ∩ near j ⊆ near j)
      rw [card_insert_of_notMem nj, Nat.succ_mul]
      change (S \ near j).card ≤ I.card*χ at hcard
      have := degree j
      omega

end YM.Integration.InletSusceptibility
