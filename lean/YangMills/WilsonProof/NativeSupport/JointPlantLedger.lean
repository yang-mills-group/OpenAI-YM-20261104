import YangMills.WilsonProof.NativeSupport.JointBornIntake
import YangMills.WilsonProof.NativeSupport.JointOldClosure
import YM.RGGapR2.Harrier

/-! Replant genuine new local factors in a proper inherited packet on an
actual nonlinear scalar report. Vacuum dirty components remain in the
gas when fresh regular and dirty inputs are separated. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Lattice RG Wilson Marker Extra.Trajectories MergeProof MergeProof.Accent
open RGGapR2 MeasureTheory Packet Painted
open scoped Classical BigOperators
variable {V J : Type} [Fintype V] [DecidableEq V] [Fintype J] {G:Gauge} {n:Side}
variable (R:Rep G n) (B:Census V) (o:V → Site n)
variable (H:Support n → Config G n → Poly B) (K:Box n → Config G n → Poly B)
variable (birth:J → V) (X:J → Support n) (v:J → Config G n → ℂ)

def plantedLog := H+tally X (fresh R B birth X v true)
def plantedFull := closure (exclaim R.activities B+K) (fresh R B birth X v false) X R.p.threshold
def plantedDirty (i:Box n) (Z:Config G n) := Rough.purge B (plantedFull R B K birth X v i Z)

omit [Fintype V] in
private theorem live_left_or_right {a b:Poly B} (h:a+b≠0) : a≠0 ∨ b≠0 := by
  by_contra! no
  exact h (by rw [no.1,no.2,zero_add])

theorem plant_ledger {a quiet ue uk freshCost:ℝ} (vac:R.activities.Valid R.p a quiet)
    (inherited:Rough.Ledger o H K R.p.threshold) (w:V → ℝ) (hw:∀ j,0 < w j)
    (ht:Towed w id H R.p.B (R.p.supportExponent-1) ue)
    (kt:Towed w Prod.fst K R.p.B (R.p.supportExponent-1) uk)
    (borne:∀ good j,Borne o (X j) (fresh R B birth X v good j) R.p.threshold)
    (freshPaid:∀ good,Towed w X (fresh R B birth X v good) R.p.B (R.p.supportExponent-1) freshCost)
    (exp0 : 0 ≤ R.p.supportExponent-4)
    (reserve:((R.p.B+R.p.B+1:ℕ):ℝ)^4*(quiet+uk+freshCost) ≤ 3) :
    let E := plantedLog R B H birth X v
    let K' := plantedDirty R B K birth X v
    Rough.Ledger o E K' R.p.threshold ∧
    Towed w id E R.p.B (R.p.supportExponent-4) (ue+freshCost) ∧
    Towed w Prod.fst K' R.p.B (R.p.supportExponent-4) (Real.exp (quiet+uk+freshCost)-1) ∧
    (exclaim R.activities B+K'=plantedFull R B K birth X v) ∧
    ∀ Z,play R B (exclaim R.activities B+K') (fun U=>∑ i,E i U) Z =
      play R B (exclaim R.activities B+K) (fun U=>∑ i,H i U) Z *
        ∏ j,(1+Poly.send (B.fire (birth j)) (v j Z)) := by
  intro E K'
  let raw := fresh R B birth X v
  let gas := exclaim R.activities B+K
  have noQuiet good j Z : (raw good j Z).part B.quiet=0 := by simp [raw,fresh,Ne.symm (B.fire_hot (birth j))]
  have burn j : Burns o (X j) (raw true j) R.p.threshold := by
    refine ⟨borne true j,fun Z hit=>?_,noQuiet true j⟩
    by_contra lost
    exact hit (by simp [raw,fresh,lost])
  have eb (i:Support n) : Burns o i (tally X (raw true) i) R.p.threshold :=
    transitE X (r:=id) burn (fun _=>Summable.of_finite) i
  have eboth (i:Support n) : Burns o i (E i) R.p.threshold := by
    refine ⟨Harrier.Borne.plusB B i i (inherited.exp i).toBorne (eb i).toBorne,fun Z nz=>?_,fun Z=>?_⟩
    · rcases live_left_or_right B nz with yes|yes
      · exact (inherited.exp i).permits Z yes
      · exact (eb i).permits Z yes
    · change (H i Z+tally X (raw true) i Z).part B.quiet=0
      rw [Poly.part_plus,(inherited.exp i).sil,(eb i).sil,zero_add]
  have light := (towing X (raw true) (r:=id) (freshPaid true) hw)
  have transported := Harrier.Towed.plus' B (R:=R) ht light hw
  have original i : Flow o i (exclaim R.activities B i) R.p.threshold := granular R.activities R.p B vac i
  have legal i : Flow o i (gas i) R.p.threshold := by
    refine ⟨Harrier.Borne.plusB B i i.1 (original i).toBorne (inherited.flag i).1.toBorne,fun Z nz=>?_⟩
    rcases live_left_or_right B nz with yes|yes
    · exact (original i).permits Z yes
    · exact (inherited.flag i).1.permits Z yes
  have lawful i : Flow o i (plantedFull R B K birth X v i) R.p.threshold :=
    threshed gas (raw false) X R.p.threshold legal (borne false) i
  have gasPaid:=Harrier.Towed.plus' B (R:=R)
    ((vacant R.activities R.p B vac w hw).shrink (by linarith : R.p.supportExponent-1 ≤ R.p.supportExponent) le_rfl hw) kt hw
  have level : (R.p.supportExponent-4)+3=R.p.supportExponent-1 := by ring
  have closedPay := branch gas (raw false) X R.p.threshold w (level.symm ▸ gasPaid)
    (level.symm ▸ freshPaid false) hw exp0 reserve
  have full : exclaim R.activities B+K'=plantedFull R B K birth X v := by
    funext i Z
    ext p
    change (Poly.send B.quiet _).part p+(if p=B.quiet then 0 else _) = _
    rw [Poly.part_send]
    split_ifs with hp
    · subst p
      rw [add_zero]
      symm
      have quietId:=wine gas (raw false) X R.p.threshold Z i (fun j=>(legal j).permits Z) (fun j=>noQuiet false j Z)
      have zero := (inherited.flag i).2 Z
      change (plantedFull R B K birth X v i Z).part B.quiet=_
      have actual : (gas i Z).part B.quiet=_ := Poly.part_plus _ _ _
      rw [zero,add_zero] at actual
      exact (quietId.trans actual).trans ((Poly.part_send B.quiet B.quiet _).trans (if_pos rfl))
    · exact zero_add _
  refine ⟨⟨eboth,fun i=>⟨Rough.Flow.purge (lawful i),fun U=>(show (if B.quiet=B.quiet then (0:ℂ) else (plantedFull R B K birth X v i U).part B.quiet)=0 from if_pos rfl)⟩⟩,
    transported.shrink (by linarith) le_rfl hw,Rough.Towed.purge (R:=R) closedPay,full,?_⟩
  intro Z
  rw [full]
  have sums (U:Config G n) : ∑ i,E i U=(∑ i,H i U)+∑ j,raw true j U := by
    change (∑ i,(H i U+tally X (raw true) i U))=_
    rw [sum_add_distrib]
    apply congrArg ((∑ i,H i U)+·)
    simpa only [tally,tsum_fintype] using (border (p:=fun j=>raw true j U) X Summable.of_finite).tsum_eq
  simp_rw [sums]
  apply mount_flags R B birth X v gas (fun U=>∑ i,H i U)
  · exact fun U i hi=>((legal i).permits U hi).2
  · exact fun Z=>by rw [Poly.part_sum]; exact sum_eq_zero fun i _=>(inherited.exp i).sil Z

end YM.Integration.InletSusceptibility.JointShadow
