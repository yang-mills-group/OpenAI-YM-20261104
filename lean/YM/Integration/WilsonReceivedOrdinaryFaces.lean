import YM.Integration.WilsonReceivedPostLog
import YM.Comparison.RG02.Cumulants.Partition

/-! Turning a paid connected Wilson table into the full ordinary table
keeps the wallet of every subset in each covering partition. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedOrdinaryFaces
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Cumulants
open scoped Classical BigOperators

private theorem product {J : Type*} [DecidableEq J] (K : Finset J) (x y : J → ℂ)
    (E A : ℝ) (hE : 0 ≤ E) (hA : 1 ≤ A) (dx : ∀ j, ‖x j - y j‖ ≤ E)
    (hx : ∀ j, ‖x j‖ ≤ A) (hy : ∀ j, ‖y j‖ ≤ A) :
    ‖(∏ j∈K, x j) - ∏ j∈K, y j‖ ≤ (K.card:ℝ)*E*A^K.card := by
  have pos : 0 ≤ A := zero_le_one.trans hA
  induction K using Finset.induction_on with
  | empty => simp
  | @insert i K hi ih =>
    have base : ‖∏ j∈K, y j‖ ≤ A^K.card := by
      rw [Complex.norm_prod,←Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hy j)
    rw [card_insert_of_notMem hi,Nat.cast_succ,pow_succ,prod_insert hi,prod_insert hi]
    calc
      _ = ‖x i*((∏ j∈K,x j) - ∏ j∈K,y j)+(x i-y i)*∏ j∈K,y j‖ := by congr 1; ring
      _ ≤ ‖x i‖*‖(∏ j∈K,x j) - ∏ j∈K,y j‖ + ‖x i-y i‖*‖∏ j∈K,y j‖ := by
        simpa only [norm_mul] using norm_add_le (x i*((∏ j∈K,x j) - ∏ j∈K,y j))
          ((x i-y i)*∏ j∈K,y j)
      _ ≤ A*((K.card:ℝ)*E*A^K.card) + E*A^K.card :=
        add_le_add (mul_le_mul (hx i) ih (norm_nonneg _) pos)
          (mul_le_mul (dx i) base (norm_nonneg _) hE)
      _ ≤ A*((K.card:ℝ)*E*A^K.card) + (E*A^K.card)*A := by
        exact add_le_add le_rfl (le_mul_of_one_le_right (mul_nonneg hE (pow_nonneg pos _)) hA)
      _ = _ := by ring

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}

omit [Fintype V] in
theorem contained (s : Γ.Mode) (h : (parts Γ).Mode) (hit : h ∈ shards Γ s)
    (d : Hot Γ) (member : d ∈ h.val) : d.val.val ⊆ s.val := by
  rw [←show unionOf h = s from (mem_filter.mp hit).2]
  exact fun _ v => mem_biUnion.mpr ⟨d,member,v⟩

/-- The bound applies to the complete signed table, including its
disconnected products and constant face. The physical and predicted logs
must be centered on their own common normalized quiet coefficient. -/
theorem ordinary_on (x y : Poly Γ) (w : V → ℝ) (hw : ∀ v, 0<w v)
    (x₀ : x.part Γ.quiet = 0) (y₀ : y.part Γ.quiet = 0)
    (E M : ℝ) (hE : 0 ≤ E) (width : 1 ≤ M + E) (s : Γ.Mode)
    (change : ∀ d : Hot Γ, d.val.val ⊆ s.val → Poly.toll w d.val * ‖x.part d.val - y.part d.val‖ ≤ E)
    (filed : ∀ d : Hot Γ, d.val.val ⊆ s.val → Poly.toll w d.val * ‖y.part d.val‖ ≤ M) :
    Poly.toll w s * ‖(Poly.pass x).part s - (Poly.pass y).part s‖ ≤
      ∑ h∈shards Γ s, (h.val.card:ℝ)*E*(M+E)^h.val.card := by
  let scaled (p : Poly Γ) (d : Hot Γ) := if d.val.val ⊆ s.val then (Poly.toll w d.val : ℂ)*p.part d.val else 0
  have normed (p : Poly Γ) (d : Hot Γ) (hd : d.val.val ⊆ s.val) :
      ‖scaled p d‖ = Poly.toll w d.val * ‖p.part d.val‖ := by
    simp only [scaled,if_pos hd,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Poly.worth hw _)]
  have dx (d : Hot Γ) : ‖scaled x d - scaled y d‖ ≤ E := by
    by_cases hd : d.val.val ⊆ s.val
    · simpa only [scaled,if_pos hd,←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Poly.worth hw _)]
        using change d hd
    · simpa only [scaled,if_neg hd,sub_zero,norm_zero] using hE
  have hy (d : Hot Γ) : ‖scaled y d‖ ≤ M+E := by
    by_cases hd : d.val.val ⊆ s.val
    · exact ((normed y d hd).trans_le (filed d hd)).trans (le_add_of_nonneg_right hE)
    · simpa only [scaled,if_neg hd,norm_zero] using zero_le_one.trans width
  have hx (d : Hot Γ) : ‖scaled x d‖ ≤ M+E := by
    by_cases hd : d.val.val ⊆ s.val
    · calc
        _ ≤ ‖scaled y d‖+‖scaled x d-scaled y d‖ := by
          simpa only [add_sub_cancel] using norm_add_le (scaled y d) (scaled x d-scaled y d)
        _ ≤ _ := add_le_add ((normed y d hd).trans_le (filed d hd)) (dx d)
    · simpa only [scaled,if_neg hd,norm_zero] using zero_le_one.trans width
  rw [pass_partition _ x₀,pass_partition _ y₀,←Finset.sum_sub_distrib]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Poly.worth hw _).le).trans
  rw [mul_sum]
  apply sum_le_sum
  intro h hh
  have toll : Poly.toll w s = ∏ d∈h.val, Poly.toll w d.val := by
    rw [← show unionOf h = s from (mem_filter.mp hh).2]
    exact prod_biUnion (parts_wise h)
  have words (p : Poly Γ) : (∏ d∈h.val,scaled p d) =
      (Poly.toll w s : ℂ) * ∏ d∈h.val,p.part d.val := by
    calc
      _ = ∏ d∈h.val,(Poly.toll w d.val : ℂ)*p.part d.val :=
        prod_congr rfl fun d hd => if_pos (contained s h hh d hd)
      _ = _ := by simp only [prod_mul_distrib,toll,Complex.ofReal_prod]
  have bound := product h.val (scaled x) (scaled y) E (M+E) hE width dx hx hy
  rw [words,words,←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Poly.worth hw _)] at bound
  exact bound

theorem ordinary (x y : Poly Γ) (w : V → ℝ) (hw : ∀ v, 0<w v)
    (x₀ : x.part Γ.quiet = 0) (y₀ : y.part Γ.quiet = 0)
    (E M : ℝ) (hE : 0 ≤ E) (width : 1 ≤ M + E)
    (change : ∀ d : Hot Γ, Poly.toll w d.val * ‖x.part d.val - y.part d.val‖ ≤ E)
    (filed : ∀ d : Hot Γ, Poly.toll w d.val * ‖y.part d.val‖ ≤ M) (s : Γ.Mode) :
    Poly.toll w s * ‖(Poly.pass x).part s - (Poly.pass y).part s‖ ≤
      ∑ h∈shards Γ s, (h.val.card:ℝ)*E*(M+E)^h.val.card :=
  ordinary_on x y w hw x₀ y₀ E M hE width s (fun d _=>change d) (fun d _=>filed d)

end YM.Integration.WilsonReceivedOrdinaryFaces
