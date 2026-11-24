import YangMills.WilsonProof.NativeSupport.TerminalGas

/-! All thermal fugacities can be evaluated at once. A rooted hit controls the
actual native denominator ratio on every subset, at finite arbitrary volume. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.TerminalGas
open Finset Marker Packet
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Π₀" => Poly (Stock.census V)

omit [Fintype V] in
private lemma erase_many (z : Finset V → ℂ) (A D : Finset V)
    (step : ∀ B⊆A, ∀ x∈B, ‖z (B.erase x)‖ ≤ 2*‖z B‖) (hd : D⊆A) :
    ‖z (A\D)‖ ≤ 2^D.card * ‖z A‖ := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert t D ht ih =>
    have hx : t∈A\D := mem_sdiff.mpr ⟨hd (mem_insert_self ..),ht⟩
    rw [sdiff_insert,card_insert_of_notMem ht,pow_succ]
    calc
      _ ≤ 2*‖z (A\D)‖ := step _ sdiff_subset _ hx
      _ ≤ 2*(2^D.card * ‖z A‖) := by
        gcongr
        exact ih ((subset_insert ..).trans hd)
      _ = _ := by ring

theorem denominator (H : Π₀) (quiet : H.part (Stock.census V).quiet=0)
    (hit : ∀ x : V, ∑ T ∈ (univ : Finset (Finset V)).filter (fun T => x∈T),
      ‖H.part (tag T)‖ * 2^(T.card-1) ≤ 1/2) (A : Finset V) :
    sliceZ A (Poly.pass H) ≠ 0 ∧ ∀ x∈A,
      ‖sliceZ A (Poly.pass H)-sliceZ (A.erase x) (Poly.pass H)‖ ≤
        1/2 * ‖sliceZ (A.erase x) (Poly.pass H)‖ := by
  let z (B : Finset V) := sliceZ B (Poly.pass H)
  change z A≠0 ∧ ∀ x∈A, ‖z A-z (A.erase x)‖ ≤ 1/2*‖z (A.erase x)‖
  induction A using Finset.strongInductionOn with | _ A ih
  have row (x : V) (hx : x∈A) : ‖z A-z (A.erase x)‖ ≤ 1/2*‖z (A.erase x)‖ := by
    let B := A.erase x
    have lt : B ⊂ A := erase_ssubset hx
    have small (C : Finset V) (hc : C⊆B) (y : V) (hy : y∈C) :
        ‖z (C.erase y)‖ ≤ 2*‖z C‖ := by
      have h := (ih C (lt_of_le_of_lt hc lt)).2 y hy
      have tr : ‖z (C.erase y)‖ ≤ ‖z C-z (C.erase y)‖+‖z C‖ := by
        calc
          _ = ‖(z (C.erase y)-z C)+z C‖ := by rw [sub_add_cancel]
          _ ≤ _ := by simpa only [norm_sub_rev (z (C.erase y)) (z C)] using norm_add_le (z (C.erase y)-z C) (z C)
      linarith
    let F := (univ : Finset (Finset V)).filter fun T => x∈T
    have dec : z A-z B = ∑ T ∈ F, if T⊆A then H.part (tag T)*z (A\T) else 0 := by
      exact sub_eq_iff_eq_add.mpr ((deletion H quiet A x).trans (add_comm ..))
    rw [dec]
    calc
      _ ≤ ∑ T ∈ F, ‖if T⊆A then H.part (tag T)*z (A\T) else 0‖ := norm_sum_le ..
      _ ≤ ∑ T ∈ F, (‖H.part (tag T)‖*2^(T.card-1))*‖z B‖ := by
        apply sum_le_sum
        intro T ht
        have hxt := (mem_filter.mp ht).2
        by_cases hc : T⊆A
        · rw [if_pos hc,norm_mul,mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          have sub : T.erase x⊆B := erase_subset_erase x hc
          have hm := erase_many z B (T.erase x) small sub
          have e : B\(T.erase x)=A\T := by
            ext y; simp only [B,mem_sdiff,mem_erase]
            constructor
            · rintro ⟨⟨ne,ha⟩,nt⟩; exact ⟨ha,fun hy => nt ⟨ne,hy⟩⟩
            · rintro ⟨ha,nt⟩
              exact ⟨⟨fun he => nt (he ▸ hxt),ha⟩,fun hy => nt hy.2⟩
          rwa [e,card_erase_of_mem hxt] at hm
        · rw [if_neg hc,norm_zero]; positivity
      _ = (∑ T ∈ F, ‖H.part (tag T)‖*2^(T.card-1))*‖z B‖ := (sum_mul ..).symm
      _ ≤ 1/2*‖z B‖ := mul_le_mul_of_nonneg_right (hit _) (norm_nonneg _)
  refine ⟨?_,row⟩
  by_cases he : A.Nonempty
  · obtain ⟨x,hx⟩ := he
    have h := row x hx
    have pos := norm_pos_iff.mpr (ih (A.erase x) (erase_ssubset hx)).1
    intro bad
    rw [bad,zero_sub,norm_neg] at h
    linarith
  · rw [not_nonempty_iff_eq_empty.mp he]
    change (∑ S ∈ (∅ : Finset V).powerset, (Poly.pass H).part (tag S)) ≠ 0
    simp only [powerset_empty,sum_singleton]
    have e : tag (∅ : Finset V) = (Stock.census V).quiet := rfl
    rw [e, Poly.pass_part H quiet]
    exact one_ne_zero

theorem add_physical (H : Π₀) (quiet : H.part (Stock.census V).quiet=0)
    (hit : ∀ x : V, ∑ T ∈ (univ : Finset (Finset V)).filter (fun T => x∈T),
      ‖H.part (tag T)‖ * 2^(T.card-1) ≤ 1/2) (thermal physical : Finset V)
    (sep : Disjoint thermal physical) :
    ‖sliceZ (thermal∪physical) (Poly.pass H) / sliceZ thermal (Poly.pass H)‖ ≤
      (3/2:ℝ)^physical.card := by
  let z (B : Finset V) := sliceZ B (Poly.pass H)
  have absPrice : ‖z (thermal∪physical)‖ ≤ (3/2:ℝ)^physical.card*‖z thermal‖ := by
    induction physical using Finset.induction_on with
    | empty => simp
    | @insert x D hx ih =>
      have hd := sep.mono_right (subset_insert x D)
      let B := thermal∪D
      have nx : x∉B := notMem_union.mpr ⟨fun ht=>disjoint_left.mp sep ht (mem_insert_self ..),hx⟩
      have step := (denominator H quiet hit (insert x B)).2 x (mem_insert_self ..)
      change ‖z (insert x B)-z ((insert x B).erase x)‖ ≤ _ at step
      simp only [erase_insert nx] at step
      have tr := norm_add_le (z (insert x B)-z B) (z B)
      rw [sub_add_cancel] at tr
      rw [union_insert,card_insert_of_notMem hx,pow_succ]
      calc
        ‖z (insert x B)‖ ≤ (3/2)*‖z B‖ := by linarith
        _ ≤ (3/2)*((3/2:ℝ)^D.card*‖z thermal‖) :=
          mul_le_mul_of_nonneg_left (ih hd) (by norm_num)
        _ = _ := by ring
  rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr (denominator H quiet hit thermal).1)]
  exact absPrice

end YM.Integration.InletSusceptibility.TerminalGas
