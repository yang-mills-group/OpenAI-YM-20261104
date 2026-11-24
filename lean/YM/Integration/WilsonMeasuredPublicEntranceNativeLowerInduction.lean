import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerEntry
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerInduction
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free PertExtension.Rigidity.Positive
open scoped Classical Topology

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

open WilsonMeasuredPublicEntranceBranchGap (watches)
open WilsonPhysicalPositionAdmissible (Native)
theorem step {d:ℕ}(Z:Module.End ℂ (D d))(native:Native C Z)
    (iso:∀x,positive C.labels (hierarchy C.labels) (Z x) (Z x)=positive C.labels (hierarchy C.labels) x x)
    (prior:∀e (he:e<d)(v:D e),Z ((scheme C.labels).rise he.le v)=(scheme C.labels).rise he.le v)
    (price:WilsonMeasuredPublicEntranceBranchGap.Axis C d→ℝ)(nonneg:∀i,0≤price i)
    (top:∀i j:WilsonMeasuredPublicEntranceBranchGap.Axis C d,watches C i j→let B:=Extra.FD.recorded C.labels d
      (B.w j).1=d→B.b.coord i (Z (B.b j)-(price j:ℂ) • B.b j)=0):Z=1:=by
  let B:=Extra.FD.recorded C.labels d
  let fee(j:WilsonMeasuredPublicEntranceBranchGap.Axis C d):ℝ:=if j≠0 ∧ (B.w j).1=d then price j else 1
  apply WilsonMeasuredPublicEntranceRegisteredFlag.original Z native iso fee
  · intro j
    dsimp only [fee]
    split <;> first | exact nonneg j | exact zero_le_one
  · simp [fee]
  · intro i j seen
    change B.b.coord i (Z (B.b j)-(fee j:ℂ) • B.b j)=0
    by_cases h:(B.w j).1=d
    · simpa only [fee,if_pos (And.intro seen.1 h)] using top i j seen h
    · have lower:(B.w j).1<d:=(B.cap j).lt_of_ne h
      obtain ⟨v,hv⟩:=WilsonMeasuredPublicEntranceRecordedQuotient.own B j
      have fix:Z (B.b j)=B.b j:=by rw [←hv];exact prior _ lower v
      have no:¬(j≠0 ∧ (B.w j).1=d):=fun hh=>h hh.2
      simp only [fee,if_neg no,Complex.ofReal_one,one_smul,fix,sub_self,map_zero]

theorem original {k:ℕ}(Z:(d:ℕ)→d≤k→Module.End ℂ (D d))
    (native:∀d hd,Native C (Z d hd))
    (iso:∀d hd x,positive C.labels (hierarchy C.labels) (Z d hd x) (Z d hd x)=positive C.labels (hierarchy C.labels) x x)
    (natural:∀d (hd:d≤k) e (he:e<d)(v:D e),Z d hd ((scheme C.labels).rise he.le v)=
      (scheme C.labels).rise he.le (Z e (he.le.trans hd) v))
    (price:∀d,d≤k→WilsonMeasuredPublicEntranceBranchGap.Axis C d→ℝ)(nonneg:∀d hd i,0≤price d hd i)
    (top:∀d (hd:d≤k)(i j:WilsonMeasuredPublicEntranceBranchGap.Axis C d),watches C i j→let B:=Extra.FD.recorded C.labels d
      (B.w j).1=d→B.b.coord i (Z d hd (B.b j)-(price d hd j:ℂ) • B.b j)=0):∀d (hd:d≤k),Z d hd=1:=by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    apply step (Z d hd) (native d hd) (iso d hd) _ (price d hd) (nonneg d hd) (top d hd)
    intro e he v
    rw [natural d hd e he,ih e he (he.le.trans hd)]
    rfl
end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerInduction
end
