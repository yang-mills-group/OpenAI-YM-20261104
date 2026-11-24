import YangMills.WilsonProof.NativeSupport.JointPlantLedger
import YangMills.WilsonProof.NativeSupport.JointProjectedTransfer

/-! Reconstruct the proper pair on the previous primitive alphabet after
the original forced (dirty) sheet has been projected. Its quiet part is
exactly the outgoing original activities. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Lattice RG Wilson Marker MergeProof MergeProof.Accent RGGapR2 Packet Painted
open scoped Classical BigOperators
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq V] {G:Gauge} {n:Side}
local notation "C" => Stock.census (Ink V)
local notation "B" => Stock.census V

def RootedSheet (P:BudgetPoint) (X:I → Support n) (F:I → Config G n → Marker.Poly (Stock.census V)) (w:V → ℝ) (u:ℝ) : Prop :=
  ∃ c:I → Finset V → ℝ, (∀ i s,0 ≤ c i s) ∧ (∀ i Z s,‖(F i Z).part (tag s)‖ ≤ c i s) ∧
    ∀ y:V,(∑ i,Real.exp (P.supportExponent*coverNumber P.B (X i))*
      ∑ s:Finset V with y∈s,Poly.toll w (tag s)*c i s) ≤ u

theorem rooted_purge {P:BudgetPoint} {X:I → Support n} {F:I → Config G n → Poly B} {w:V → ℝ} {u:ℝ}
    (h:RootedSheet P X F w u) : RootedSheet P X (fun i Z=>Rough.purge B (F i Z)) w u := by
  obtain ⟨c,nc,val,root⟩:=h
  refine ⟨c,nc,fun i Z s=>?_,root⟩
  change ‖(if tag s=(Stock.census V).quiet then 0 else (F i Z).part (tag s))‖ ≤ c i s
  split
  · rw [norm_zero]; exact nc i s
  · exact val .. 

variable (R:Rep G n) (o:V → Site n)
variable (E:Support n → Config G n → Marker.Poly (Stock.census (Ink V))) (K:Box n → Config G n → Marker.Poly (Stock.census (Ink V)))
theorem projected_ledger
    (regular:∀ i,Burns (o ∘ Prod.fst) i (E i) R.p.threshold)
    (dirty:∀ i,Flow (o ∘ Prod.fst) i (K i) R.p.threshold)
    (vacuum:∀ i Z,(K i Z).part (Stock.census (Ink V)).quiet=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i Z) :
    let E' i Z:=project (E i Z)
    let K' i Z:=Rough.purge B (project (K i Z))
    Rough.Ledger o E' K' R.p.threshold ∧
    ∀ Z,project (play R C K (fun U=>∑ i,E i U) Z)=play R B (exclaim R.activities B+K') (fun U=>∑ i,E' i U) Z := by
  intro E' K'
  have er (i:Support n) : Burns o i (E' i) R.p.threshold := by
    refine ⟨born_project _ (regular i).toBorne,fun Z hit=>(regular i).permits Z ?_,fun Z=>(project_quiet _).trans ((regular i).sil Z)⟩
    exact fun blank=>hit (by change project (E i Z)=0; rw [blank,map_zero])
  have dk (i:Box n) : Flow o i (fun Z=>project (K i Z)) R.p.threshold := by
    refine ⟨born_project _ (dirty i).toBorne,fun Z hit=>(dirty i).permits Z ?_⟩
    exact fun blank=>hit (by rw [blank,map_zero])
  have full : exclaim R.activities B+K'=(fun i Z=>project (K i Z)) := by
    funext i Z
    ext s
    change (Poly.send (Stock.census V).quiet _).part s+
      (if s=(Stock.census V).quiet then 0 else (project (K i Z)).part s)=(project (K i Z)).part s
    rw [Poly.part_send]
    by_cases eq:s=(Stock.census V).quiet
    · rw [if_pos eq,if_pos eq,add_zero,eq]
      exact ((project_quiet _).trans (vacuum i Z)).symm
    · rw [if_neg eq,if_neg eq,zero_add]
  refine ⟨⟨er,fun i=>⟨Rough.Flow.purge (dk i),fun Z=>(show (if (Stock.census V).quiet=(Stock.census V).quiet then (0:ℂ) else (project (K i Z)).part (Stock.census V).quiet)=0 from if_pos rfl)⟩⟩,fun Z=>?_⟩
  rw [full,project_play]
  · simp only [map_sum,E']
  · rw [Poly.part_sum]
    exact sum_eq_zero fun i _=>(regular i).sil Z

end YM.Integration.InletSusceptibility.JointShadow
