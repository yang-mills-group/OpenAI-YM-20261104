import YM.Integration.QLocalPhysicalBirthTowing

/-! Recover any specific unnormalized original marked row. Each occupied
marker radius is restored exactly once. Even the tested configurations may
be chosen independently on different physical output barcodes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalMarkedIncidence
open Function Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums MergeProof.Ribbon
open Packets Push.GridApprox.Nil Push.AbsoluteSums
open scoped BigOperators Classical

private theorem scale {ι : Type*} {f : ι → ℝ} {a c : ℝ} (ha : 0 ≤ a) (h : SumBudget f c) :
    SumBudget (fun i => a*f i) (a*c) := by
  refine ⟨fun i => mul_nonneg ha (h.1 i), h.2.1.mul_left a, ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left h.2.2 ha

variable {V : Type} [DecidableEq V] [Fintype V] {n : Side}

theorem recover {G : Gauge} {X : Box n → Support n} {k : ℕ} {a c : ℝ}
    (F : Box n → Config G n → Poly (Ribbon.Bud V)) (B : Box n → Sheet (Ribbon.Bud V))
    (w : V → ℝ) (hw : ∀ i, 0 < w i) (hB : ∀ s, 0 ≤ B s)
    (hf : ∀ s U q, ‖(F s U).part q‖ ≤ B s q) (h : Ac.Hit X k (fun s => wordsPrice w (B s)) a c)
    (q : (Ribbon.Bud V).Mode) (U : Box n → Config G n) :
    Ac.Hit X k (fun s => ‖(F s (U s)).part q‖) a (c / Poly.toll w q) := by
  intro x
  have hp := Poly.worth hw q
  have hs := scale (inv_nonneg.mpr hp.le) (h x)
  rw [div_eq_inv_mul]
  apply budget_mono hs
  · intro s
    split
    · exact mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
    · rfl
  · intro s
    by_cases hx : x ∈ X s
    · simp only [if_pos hx]
      have hq : Poly.toll w q * B s q ≤ wordsPrice w (B s) :=
        Finset.single_le_sum (fun j _ => mul_nonneg (Poly.worth hw j).le (hB s j)) (mem_univ q)
      have hpaid : B s q ≤ (Poly.toll w q)⁻¹ * wordsPrice w (B s) := by
        rw [← div_eq_inv_mul,le_div_iff₀ hp,mul_comm]
        exact hq
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right ((hf s (U s) q).trans hpaid) (Real.exp_nonneg _)
    · simp only [if_neg hx,mul_zero,le_refl]

variable {G : Gauge} (R : Run G) (N p L : ℕ) (o : Positions V (R.family.side L p))
  (d : V → ℕ) (v : ∀ i, R.family.label (d i))
local notation "P₀" => R.family.path.rep N p L
local notation "Z₀" => ActualRunUnmaskedPartners.actualInput R N p L o d v
local notation "D₀" => NativeCaptionDeck.Input.deck Z₀ (BudgetPoint.threshold (Rep.p P₀))

theorem actual (hL : L ≤ N) (href : ∀ i, R.family.ref (d i) ≤ L)
    (b : ℕ → ℝ) (hs : Summable b) (hb : ∀ i U, ‖(P₀).activities.K i U‖ ≤ b i)
    (w : V → ℝ) (hw : ∀ i, 0 < w i) {a e g : ℝ} (ha : 0 ≤ a)
    (h : Ac.Hit (D₀).cover (P₀).p.B (QLocalPhysicalBirthTowing.markedToll R N p L o d v b w) (a+e) g)
    (hsmall : (((P₀).p.B + (P₀).p.B + 1 : ℕ) : ℝ)^4 * g ≤ e)
    (q : (Ribbon.Bud V).Mode) (U : Box (R.family.side L p) → Config G (R.family.side L p)) :
    Ac.Hit Prod.fst (P₀).p.B (fun s => ‖(ActualRunUnmaskedPartners.actualCorrection R N p L o d v s (U s)).part q‖)
      a ((Real.exp g-1)/Poly.toll w q) := by
  obtain ⟨B,hB,hf,hprice⟩ := QLocalPhysicalBirthTowing.sheet R N p L o d v hL href b hs hb w hw ha h hsmall
  exact recover _ B w hw hB hf hprice q U

end YM.Integration.QLocalPhysicalMarkedIncidence
end
