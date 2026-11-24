import YM.Integration.OriginalMarkedSupportMass
import YM.Next.SCHEDULE.Support

/-! Local changes of the full masked additive series. The native flag tests
inspect one plaquette layer around the sites on which links are changed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedLocalDifference

open Function Lattice Lattice.Corona RG Wilson Push.GridApprox.Attach
open scoped Classical BigOperators

variable {G : Gauge} {n : Side}

/-- All oriented links based outside the specified changed sites agree. -/
def Outside (S : Support n) (U V : Config G n) : Prop :=
  ∀ e : Edge (Site n), e.1∉S → U e=V e

theorem inspected_outside {S X : Support n} {U V : Config G n} (outside : Outside S U V)
    (disjoint : Disjoint X (halo 8 S)) : Agrees (inspected X) U V := by
  intro e htail _
  apply outside e
  intro hS
  obtain ⟨x,hx,hy⟩ := halo_spec.mp (Next.Scheduling.flag_layer X htail)
  exact (Finset.disjoint_left.mp disjoint hx) (halo_spec.mpr ⟨e.1,hS,by rwa [separation_comm]⟩)

variable (A : Activities G n) (p : BudgetPoint)

private theorem inspected_row (reg : A.RegularFamily p) (i : ℕ) :
    LocalOn (inspected (A.reg i).support) (A.regularOccurrence p i) := by
  apply UsesFinal.allReads p.threshold (A.reg i).support (A.regularOccurrence p i)
  intro U V eq hflags
  have mask : Healthy p.threshold (A.reg i).support U ↔ Healthy p.threshold (A.reg i).support V := by
    simp only [Healthy,Finset.disjoint_iff_inter_eq_empty]
    rw [hflags]
  unfold Activities.regularOccurrence
  by_cases h : Healthy p.threshold (A.reg i).support U
  · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (mask.mp h)]
    exact (reg.smooth i).sites U V eq
  · rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt mask.mpr h)]

private theorem abs_row {i : ℕ} {k : ℝ}
    (h : p.supBounds (A.reg i).site (A.reg i).support (A.E i) k) (U : Config G n) :
    ‖A.regularOccurrence p i U‖≤k := by
  by_cases healthy : Healthy p.threshold (A.reg i).support U
  · rw [Activities.regularOccurrence,masked_eq _ _ _ _ healthy]
    exact h.2 U healthy [] (Nat.zero_le _) (by simp)
  · rw [Activities.regularOccurrence,masked_ne _ _ _ _ healthy,norm_zero]
    exact h.1

private theorem summable {ε : ℝ} (budget : A.EBound p ε) (U : Config G n) :
    Summable (fun i => A.regularOccurrence p i U) := by
  obtain ⟨b,sums,prices⟩ := Activities.E_total budget
  exact sums.of_norm_bounded (fun i => abs_row A p (prices i) U)

/-- The only spatial factor is the number of sites actually changed times a
fixed four-dimensional halo size. This holds even when either field is dirty. -/
theorem variation {ε : ℝ} (reg : A.RegularFamily p) (budget : A.EBound p ε)
    (r : ℕ) (hr : 1≤p.supportExponent*r) (S : Support n) (U V : Config G n)
    (outside : Outside S U V) :
    |A.additive p U-A.additive p V| ≤ 2*((S.card:ℝ)*(17:ℝ)^4*(hitConstant ((p.B+1)*r)*ε)) := by
  have u := summable A p budget U
  have v := summable A p budget V
  obtain ⟨b,cap,roots⟩ := budget
  let H := halo 8 S
  let bill (i : ℕ) := if ¬Disjoint (A.reg i).support H then b i else 0
  let term (i : ℕ) := A.regularOccurrence p i U-A.regularOccurrence p i V
  have price : SumBudget bill ((H.card:ℝ)*(hitConstant ((p.B+1)*r)*ε)) :=
    OriginalMarkedSupportMass.carrier A p b (fun i => (cap i).1) roots H r hr
  have point (i : ℕ) : ‖term i‖≤2*bill i := by
    by_cases he : Disjoint (A.reg i).support H
    · have same := inspected_row A p reg i U V (inspected_outside outside he)
      have zero : bill i=0 := if_neg (not_not_intro he)
      have untouched : term i=0 := sub_eq_zero.mpr same
      rw [untouched,zero,norm_zero,mul_zero]
    · have amount : bill i=b i := if_pos he
      rw [amount]
      calc ‖term i‖ ≤ ‖A.regularOccurrence p i U‖+‖A.regularOccurrence p i V‖ := norm_sub_le .. 
           _ ≤ b i+b i := add_le_add (abs_row A p (cap i) U) (abs_row A p (cap i) V)
           _ = _ := (two_mul _).symm
  have bs : Summable (fun i => 2*bill i) := price.2.1.mul_left _
  have asum := bs.of_nonneg_of_le (fun i => norm_nonneg (term i)) point
  have total : A.additive p U-A.additive p V=∑' i,term i := (u.tsum_sub v).symm
  have hε : 0≤ε := (tsum_nonneg (roots 0).1).trans (roots 0).2.2
  have hk : 0≤hitConstant ((p.B+1)*r) := by
    unfold hitConstant
    exact mul_nonneg (by positivity) (tsum_nonneg fun i => (polyExp_pos i).le)
  have halo : (H.card:ℝ)≤(S.card:ℝ)*(17:ℝ)^4 := by
    exact_mod_cast (halo_size S 8)
  rw [total,←Real.norm_eq_abs]
  calc ‖∑' i,term i‖ ≤ ∑' i,‖term i‖ := norm_tsum_le_tsum_norm asum
       _ ≤ ∑' i,2*bill i := asum.tsum_le_tsum point bs
       _ = 2*∑' i,bill i := tsum_mul_left
       _ ≤ 2*((H.card:ℝ)*(hitConstant ((p.B+1)*r)*ε)) :=
         mul_le_mul_of_nonneg_left price.2.2 (by norm_num)
       _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right halo (mul_nonneg hk hε)) (by norm_num)

end YM.Integration.OriginalMarkedLocalDifference
