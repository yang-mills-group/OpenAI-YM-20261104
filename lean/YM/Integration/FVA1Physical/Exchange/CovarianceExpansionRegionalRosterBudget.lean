import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionTwoGasComponent

/-! Generalize the native compulsory roster invoice to the prescribed subset
of flags in a connected physical component. This reuses the exact per-site
KBound and the cover_power partition estimate, with no volume factor even
when distant failures are retained on the complementary component. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Finset Set Lattice RG Wilson Push.AbsoluteSums
open Marked Marked.RemoteRoster RoseCut SectorNext.Vacuum
open YM.Integration.FVA1Physical.Round2.Curvature.Tariff.Native
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

def regionalTerm (A:Activities G n)(D:Support n)(s:Finset ℕ)(U:Fld):ℝ:=
  if Regional A D s then ∏i∈s,A.K i U else 0

theorem regional_roster_wallet (A : Activities G n) {p : BudgetPoint} {w : ℝ}
    (hw : w ≤ 1) (budget : A.KBound p w) (D : Support n)
    (U : Finset ℕ → Config G n) :
    SumBudget (fun s => rosterWeight A p s * ‖regionalTerm A D s (U s)‖)
      (if D = ∅ then 1 else w) := by
  classical
  obtain ⟨v,hv,site⟩ := budget
  let X := fun i => (A.forced i).support
  let Z := fun i => (A.forced i).inventory
  let charge := fun i => p.mass (X i) (v i)
  have nn (i : ℕ) : 0 ≤ charge i := (hv i).1.trans (p.loMass _ _ (hv i).1)
  have summ : Summable charge := by
    let q := fun (x : Site n) (i : ℕ) => if x ∈ X i then charge i else 0
    apply (summable_sum (f := fun x : Site n => q x) (s := univ) (fun x _ => (site x).2.1)).of_nonneg_of_le nn
    intro i
    obtain ⟨x,hx⟩ := (A.forced i).inventory_ne.mono (A.forced i).inventory_sup
    simpa only [q,if_pos (show x ∈ X i from hx)] using
      (single_le_sum (f := fun x => q x i) (fun x _ => (site x).1 i) (mem_univ x))
  let bill := fun s : Finset ℕ => rosterWeight A p s * ‖regionalTerm A D s (U s)‖
  have nonneg (s) : 0 ≤ bill s := mul_nonneg (roster_weight_nonneg _ _ _) (norm_nonneg _)
  have cap (s : Finset ℕ) : bill s ≤ ∏ i ∈ s, charge i := by
    dsimp only [bill,rosterWeight,regionalTerm]
    split
    · rw [norm_prod, ← prod_mul_distrib]
      exact prod_le_prod (fun i _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) fun i _ =>
        mul_le_mul_of_nonneg_left ((hv i).2 _) (Real.exp_pos _).le
    rw [norm_zero,mul_zero]
    exact prod_nonneg fun i _ => nn i
  have sums := (summable_finsetProd_of_summable_nonneg nn summ).of_nonneg_of_le nonneg cap
  refine ⟨nonneg,sums,sums.tsum_le_of_sum_le ?_⟩
  intro s
  let I := s.biUnion id
  let F := accounted X Z D
  have included : s.filter F ⊆ I.powerset.filter F := by
    intro t ht
    obtain ⟨a,b⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_powerset.mpr fun i hi => mem_biUnion.mpr ⟨t,a,hi⟩,b⟩
  calc
    _ = ∑ j ∈ s.filter F, bill j := by
      symm
      apply sum_subset (filter_subset ..)
      intro j hj omitJ
      have bad : ¬ Regional A D j := by
        intro ok
        apply omitJ
        apply mem_filter.mpr ⟨hj,?_⟩
        have equiv:Regional A D j=F j:=by
          unfold Regional F accounted X Z;congr!
        exact equiv ▸ ok
      simp only [bill,regionalTerm,if_neg bad,norm_zero,mul_zero]
    _ ≤ ∑ j ∈ I.powerset.filter F, ∏ i ∈ j, charge i :=
      (sum_le_sum fun i _ => cap i).trans
        (sum_le_sum_of_subset_of_nonneg included fun j _ _ => prod_nonneg fun i _ => nn i)
    _ ≤ _ := by
      have costs := cover_power (γ:=0) X Z (fun i => (A.forced i).inventory_sup)
        (fun i => (A.forced i).inventory_ne) hw charge nn ?hit D I
      · simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at costs
        dsimp only [F]
        apply costs.trans
        apply le_of_eq
        congr!
      case hit =>
        intro x l
        apply le_trans _ (((site x).2.1.sum_le_tsum l fun i _ => (site x).1 i).trans (site x).2.2)
        apply sum_le_sum;intro i _
        split_ifs with hz
        · simp only [zero_mul,Real.exp_zero,mul_one,charge,X,le_refl]
        · exfalso;apply ‹¬ _›;exact (A.forced i).inventory_sup hz
        · exact (nn i)
        exact le_rfl

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
