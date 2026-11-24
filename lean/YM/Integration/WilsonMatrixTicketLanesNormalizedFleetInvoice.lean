import YM.Integration.WilsonMatrixTicketLanesNormalizedFleetPrice

/-! The actual charged joint corrections keep their full spatial decay at each original site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNormalizedFleetInvoice

open OPE Strobe Yarn Vista26 Function Filter Set MeasureTheory Finset Lattice Wilson RG Push
open Marker Source Extra.Histories Extra.Multi Cells MergeProof Accent Ribbons ManyCopies
open GridApprox Analysis GridApprox.Nil Ac AbsoluteSums Motion Local Bid Overlay Patrol
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V I A : Type}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Every occupied coordinate pays for the entire marked word and its true covering number. -/
def Charge {B : Census V} [Fintype A] (o : V → Site n) (w : V → ℝ) (loc : A → Support n)
    (F : A → Config G n → Poly B) (b : ℕ) (α : ℝ) : Prop :=
  ∀ (s : B.Mode) (v : V), v ∈ s.val → ∀ U,
    (∀ i, (F i U).part s ≠ 0 → o v ∈ loc i) ∧
    ∑ i, Poly.toll w s * ‖(F i U).part s‖ * Real.exp (α * (coverNumber b (loc i) : ℝ)) ≤ 1

omit [Fintype V] in
private theorem anchored {B : Census V} [Fintype A] {o : V → Site n} {w : V → ℝ}
    {loc : A → Support n} {F : A → Config G n → Poly B} {b : ℕ} {α t : ℝ}
    (pos : ∀ i, 0 < w i) (bank : Towed w loc F b α 1)
    (scope : ∀ i, Borne o (loc i) (F i) t) : Charge o w loc F b α := by
  obtain ⟨a,_,hit,atom⟩ := bank
  intro s v member U
  have there (i) (h : (F i U).part s ≠ 0) : o v ∈ loc i := by
    by_contra no
    exact h ((scope i).scope U s (fun all => no (all member)))
  refine ⟨there,?_⟩
  have bill := hit (o v)
  have budget : SumBudget (fun i => Poly.toll w s * ‖(F i U).part s‖ *
      Real.exp (α * (coverNumber b (loc i) : ℝ))) 1 := by
    apply budget_mono bill
    · intro i
      exact mul_nonneg (mul_nonneg (Poly.worth pos s).le (norm_nonneg _)) (Real.exp_pos _).le
    · intro i
      by_cases h : (F i U).part s = 0
      · simp only [h,norm_zero,mul_zero,zero_mul]
        exact bill.1 i
      · change _ ≤ if o v ∈ loc i then a i * Real.exp (α * (coverNumber b (loc i) : ℝ)) else 0
        rw [if_pos (there i h)]
        exact mul_le_mul_of_nonneg_right ((Poly.member pos s _).trans ((atom i).fares pos |>.2 U))
          (Real.exp_pos _).le
  simpa only [tsum_fintype] using budget.2.2

theorem original {P : Brigade n V} {R : Rep G n} {Q : Config G n → Poly (Names V I)}
    {o : I → Site n} {S : I → Lamp G n} {w : I → ℝ} (bought : Fleet P R Q o S w) :
    ∃ F Z, Q = restore R (P.lamp S) (P.ray R S) F Z ∧
      Carton (P.place o) F Z R.p.threshold ∧
      Charge (P.place o) (w ∘ Prod.snd) id F R.p.B (R.p.supportExponent - 3) ∧
      Charge (P.place o) (w ∘ Prod.snd) Prod.fst Z R.p.B (R.p.supportExponent - 3) := by
  obtain ⟨F,Z,actual,feeF,feeZ,_,same⟩ := bought.sem
  exact ⟨F,Z,same,actual,anchored (fun x => bought.secure x.2) feeF
    (fun X => (actual.exp X).1.toBorne),anchored (fun x => bought.secure x.2) feeZ
    (fun X => (actual.flag X).1.toBorne)⟩

end YM.Integration.WilsonMatrixTicketLanesNormalizedFleetInvoice
