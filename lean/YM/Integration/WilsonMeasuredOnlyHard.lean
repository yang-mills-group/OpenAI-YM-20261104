import YM.Integration.WilsonMeasuredCoefficientTransport
import YM.Integration.WilsonPhysicalMarkedDefectRegularProjection

/-! Erasing just the coefficient's marked hard entry leaves one genuine
forced numerator, with the original quiet hard family kept in both terms. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredOnlyHard
open Function Finset Lattice Wilson RG Source Labels Push.Local
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {h : ℕ} {F : Frame G h}

theorem original (q : Coefficient F n) (P W : Rep G n) (same : P.p=W.p) (quiet : W.eval=P.eval)
    (owners : P.activities.forced=W.activities.forced) (S : SectionData F) (Y : Hol G) (y : Site n)
    (κ M : ℝ) (f : q.Format y Y W) (r : q.remBound y W κ M) :
    (soft q).Format y Y P ∧ (soft q).remBound y P κ M ∧
    (∀ U,q.density y S W U=(soft q).density y S P U+account q W U) ∧
    ∀ U,account q W U≠0 → ∃i,q.forced i U≠0 ∧ y∈(P.activities.forced i).support ∧
      ∃z,z∈(P.activities.forced i).inventory ∧ z∈flags P.p.threshold U :=by
  have native:=formats q P W same owners f
  refine ⟨format q y P Y native,bill q y P (rent q P W same owners r),?_,?_⟩
  · intro U
    have value : q.exponentialEntry y S P U=q.exponentialEntry y S W U:=by
      simp only [Coefficient.exponentialEntry,Coefficient.maskedTerm,same]
    rw [density q y P S U,value]
    simp only [Coefficient.density,account,quiet]
  · intro U observed
    have seen : ∃i,q.forced i U≠0:=by
      by_contra! absent
      have vanished (b : Finset ℕ) : q.marked W b U=0 :=by
        unfold Coefficient.marked
        split
        · simp only [absent,zero_mul,sum_const_zero]
        · rfl
      exact observed (by simp only [account,vanished,tsum_zero,mul_zero])
    obtain ⟨i,hi⟩:=seen
    obtain ⟨z,hz⟩:=(P.activities.forced i).inventory_ne
    have charged:=native.forcing i U hi
    exact ⟨i,hi,native.carried i (fun h=>hi (congrFun h U)),z,hz,
      (mem_inter.mp (charged.1.symm ▸ hz)).2⟩

end YM.Integration.WilsonMeasuredOnlyHard
