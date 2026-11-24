import YM.Integration.WilsonSeparatedPrefixCanonicalPostAdd
import YM.Integration.WilsonOriginalDepositedHard
import YM.Integration.WilsonPhysicalHistoryGroupedEligibility

/-! The honest singleton forced profile of the canonical reporter has its
small raw one-divisor price on its original barcodes, before any gas sum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalForced
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Ac Marker Push Push.AbsoluteSums
open GridApprox.Nil QuadraticLocal Extra.Histories Labels Source MergeProof MergeProof.Accent
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V:Type} [Fintype V] [DecidableEq V] {J:Census V}
  {d:ℕ}{F:Frame G d} {P:Rep G n} {o:V → Site n} (v:V) (q:Coefficient F n)
def named (i:ℕ)(U:Config G n):Poly J:=Poly.send (J.fire v) (q.forced i U)

omit [Fintype V] in
theorem stored (w:V → ℝ) (wp:∀i,0<w i) {κ B:ℝ} (expo:0 ≤ P.p.supportExponent)
    (fee:q.remBound (o v) P κ B):
    Towed w (fun i=>(P.activities.forced i).support) (named (J:=J) v q) P.p.B P.p.supportExponent (w v*(κ*B)) := by
  obtain ⟨a,b,ha,hb,total,hκ,_,e,cap,reading⟩:=fee
  let node (i:ℕ):=(P.activities.forced i).support
  have ep i : 0 ≤ e i := (reading i).1
  have regional: Hit node P.p.B (fun i=>w v*e i) P.p.supportExponent (w v*(κ*B)) := by
    intro x
    apply budget_of_sum
    · intro i
      split
      · exact mul_nonneg (mul_nonneg (wp _).le (ep i)) (Real.exp_nonneg _)
      · exact le_rfl
    · intro E
      have single i : (if x∈node i then w v*e i*Real.exp (P.p.supportExponent*coverNumber P.p.B (node i)) else 0) ≤
          w v*P.p.mass (node i) (e i) := by
        by_cases h:x∈node i
        · rw [if_pos h];unfold BudgetPoint.mass;exact le_of_eq (by ring)
        · rw [if_neg h]
          exact mul_nonneg (wp v).le (mul_nonneg (Real.exp_nonneg _) (ep i))
      exact (Finset.sum_le_sum (fun i _=>single i)).trans
        ((budget_sum (budget_scale (wp v).le cap) E).trans
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show b≤B by linarith) hκ.le) (wp v).le))
  have sales:=(RG3.Letters.Frame.from_hit P.p.B _ _ _ (fun i=>(P.activities.forced i).inventory_ne.mono
    (P.activities.forced i).inventory_sup) (fun i=>mul_nonneg (wp _).le (ep i)) expo regional).2.1
  refine ⟨_,sales,regional,fun i=>⟨fun m=>if m=J.fire v then e i else 0,?_,?_,?_⟩⟩
  · intro m
    change 0 ≤ if m=J.fire v then e i else 0
    split <;> first | exact ep i | exact le_rfl
  · intro U m
    change ‖(Poly.send (J.fire v) (q.forced i U)).part m‖ ≤ _
    rw [Poly.part_send]
    by_cases h:m=J.fire v
    · simpa only [if_pos h] using (reading i).2 U
    · simp [h]
  · simp [wordsPrice,mul_ite]

omit [Fintype V] in
theorem board {A:Hol G} (fit:q.Format (o v) A P) (j:ℕ):
    Flow o (barcode P.activities j) (named (J:=J) v q j) P.p.threshold := by
  refine ⟨⟨fun U W ha hf=>congrArg (Poly.send (J.fire v)) (fit.supported j U W ha hf),
    fun h U=>congrArg (Poly.send (J.fire v)) (fit.invariant j h U),?_,?_⟩,?_⟩
  · intro m
    change Measurable (fun U=>(Poly.send (J.fire v) (q.forced j U)).part m)
    by_cases e:m=J.fire v
    · simpa only [Poly.part_send,if_pos e] using fit.borel j
    · simp only [Poly.part_send,if_neg e]
      exact measurable_const
  · intro U m outside
    rw [named,Poly.part_send]
    split
    next h =>
      subst m
      by_contra nz
      apply outside
      intro u inside
      obtain rfl : u=v := Finset.mem_singleton.mp inside
      exact fit.carried j (fun h=>nz (congrFun h U))
    next => rfl
  · intro U hit
    have nz:q.forced j U ≠ 0 := fun h=>hit (by simp [named,h])
    exact ⟨(fit.forcing j U nz).1,(P.activities.forced j).inventory_ne,(P.activities.forced j).inventory_sup⟩

omit [Fintype V] in
theorem original {A:Hol G} (fit:q.Format (o v) A P) (w:V → ℝ) (wp:∀i,0<w i)
    {κ B:ℝ} (expo:0 ≤ P.p.supportExponent) (fee:q.remBound (o v) P κ B):
    let h:=fun b U=>Poly.send (J.fire v) (profile P.activities q.forced b U)
    Towed w Prod.fst h P.p.B P.p.supportExponent (w v*(κ*B)) ∧
      ∀b,Flow o b (h b) P.p.threshold := by
  intro h
  have before:=stored (J:=J) v q w wp expo fee
  have exactAt : tally (barcode P.activities) (named (J:=J) v q)=h := by
    funext b U
    ext m
    rw [show (tally (barcode P.activities) (named (J:=J) v q) b U).part m=
      ∑' i:{i//barcode P.activities i=b},(named (J:=J) v q i.val U).part m from
      Poly.share ((before.repair wp U).2.comp_injective Subtype.val_injective) m]
    by_cases e:m=J.fire v
    · simp only [named,h,Poly.part_send,if_pos e];rfl
    · simp only [named,h,Poly.part_send,if_neg e,tsum_zero]
  rw [←exactAt]
  exact ⟨towing (barcode P.activities) (named (J:=J) v q) before wp,
    transitK (barcode P.activities) (r:=id) (board (J:=J) v q fit) (fun U=>(before.repair wp U).2)⟩
end YM.Integration.WilsonSeparatedPrefixCanonicalForced
end
