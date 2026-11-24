import YM.Integration.QLocalBarcodeIncidence
import YM.Push.LOCAL_SPLITTING.Budget

/-! Sitewise and barcodewise prices for every signed difference of original
live K rows with the same inventory. The test can vary by original address. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalQuietDifferenceInvoice
open Function Finset Lattice Wilson RG Marker FVA1
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Ribbon Packets Push.GridApprox.Nil Push.AbsoluteSums
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} (P Q : Rep G n)

def Receipt (cost : ℝ) : Prop :=
    ∃ b : ℕ → ℝ, Summable b ∧ (∀ i, 0 ≤ b i) ∧
      (∀ i U, ‖(P.activities.K i U : ℂ) - (Q.activities.K i U : ℂ)‖ ≤ b i) ∧
      Ac.Hit (fun i => (P.activities.forced i).support) P.p.B b P.p.supportExponent cost ∧
      Ac.Hit Prod.fst P.p.B (QLocalPhysicalBirthInvoice.barcodePrice P.activities b) P.p.supportExponent cost ∧
      ∀ U : ℕ → Config G n, Ac.Hit (fun i => (P.activities.forced i).support) P.p.B
        (fun i => ‖(P.activities.K i (U i) : ℂ) - (Q.activities.K i (U i) : ℂ)‖) P.p.supportExponent cost

theorem Receipt.mono {c d : ℝ} (h : Receipt P Q c) (hc : c ≤ d) : Receipt P Q d := by
  obtain ⟨b,hs,hb,hf,hraw,hbox,hU⟩ := h
  have lift {ι : Type} {X : ι → Support n} {v : ι → ℝ} (h : Ac.Hit X P.p.B v P.p.supportExponent c) :
      Ac.Hit X P.p.B v P.p.supportExponent d := fun x => ⟨(h x).1,(h x).2.1,(h x).2.2.trans hc⟩
  exact ⟨b,hs,hb,hf,lift hraw,lift hbox,fun U => lift (hU U)⟩

theorem paid (hp : P.p = Q.p) (hf : P.activities.forced = Q.activities.forced) {c d : ℝ}
    (hP : P.activities.KBound P.p c) (hQ : Q.activities.KBound Q.p d) : Receipt P Q (c+d) := by
  obtain ⟨f,hf₀,hF⟩ := hP
  obtain ⟨g,hg₀,hG⟩ := hQ
  let b := fun i => f i+g i
  have hb (i) : 0 ≤ b i := add_nonneg (hf₀ i).1 (hg₀ i).1
  have hdelta i (U : Config G n) : ‖(P.activities.K i U : ℂ) - (Q.activities.K i U : ℂ)‖ ≤ b i := by
    apply (norm_sub_le ..).trans
    simpa only [Complex.norm_real] using add_le_add ((hf₀ i).2 U) ((hg₀ i).2 U)
  have h (x : Site n) : SumBudget (fun i => if x ∈ (P.activities.forced i).support then
      P.p.mass (P.activities.forced i).support (b i) else 0) (c+d) := by
    have hG' : SumBudget (fun i => if x ∈ (P.activities.forced i).support then
        P.p.mass (P.activities.forced i).support (g i) else 0) d := by simpa only [hp,hf] using hG x
    convert Push.Local.sumBudget_add (hF x) hG' using 1
    funext i
    by_cases hi : x ∈ (P.activities.forced i).support <;> simp [hi,b,BudgetPoint.mass,mul_add]
  have hhit : Ac.Hit (fun i => (P.activities.forced i).support) P.p.B b P.p.supportExponent (c+d) := by
    intro x
    simpa only [BudgetPoint.mass,mul_comm] using h x
  have hs := Activities.summable_charge (fun i => (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup) hb h
  refine ⟨b,hs,hb,hdelta,hhit,QLocalBarcodeIncidence.grouped P.p P.activities b hb h,fun U x => ?_⟩
  apply Push.Local.sumBudget_mono (hhit x) _ _ le_rfl
  · intro i
    dsimp only
    split
    · exact mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
    · rfl
  · intro i
    dsimp only
    split
    · exact mul_le_mul_of_nonneg_right (hdelta i (U i)) (Real.exp_nonneg _)
    · rfl

end YM.Integration.QLocalQuietDifferenceInvoice
end

