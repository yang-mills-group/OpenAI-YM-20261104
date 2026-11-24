import YM.PCalc.Chart

/-! The direct Wilson plaquette and the actual clipped action use exactly
the same increment under a locally cold edit, independently of all remote
flags. The global selector of every kinetic row is also frozen. The only
quadratic difference is its omitted transport square on rejected rows. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Set Finset Lattice RG Wilson Precision
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

/-- All edited bonds start in D; there is no restriction on remote flags or
on how many fundamental links in D were changed. -/
theorem cold_plaquette_profile (D:Support n)(p:BudgetPoint)(U V:Fld)
    (out:∀e:Edge (Site n),e.1∉D → U e=V e)(cu:Healthy p.threshold D U)(cv:Healthy p.threshold D V)
    (s:Signed)(x:Face (Per n)):
    G.chord (faceValue (pull s 0 U) x)=G.chord (faceValue (pull s 0 V) x) ∨
    (G.chord (faceValue (pull s 0 U) x)≤p.threshold ∧ G.chord (faceValue (pull s 0 V) x)≤p.threshold):=by
  rw [Face.send_price U x s 0 G.chord G.chord_inv (fun a g=>G.chord_conj g a),
    Face.send_price V x s 0 G.chord G.chord_inv (fun a g=>G.chord_conj g a)]
  let f:=Face.send s 0 x
  by_cases near:∃z∈touched f,z∈D
  · obtain ⟨z,touch,inside⟩:=near
    have paid (W:Fld)(cold:Healthy p.threshold D W):G.chord (faceValue W f)≤p.threshold:=
      le_of_not_gt (fun bad=>disjoint_left.mp cold inside ((flags_spec _ W z).mpr ⟨f,touch,bad⟩))
    exact Or.inr ⟨paid U cu,paid V cv⟩
  left
  apply congrArg G.chord
  change faceValue U f=faceValue V f
  apply travel_local
  intro e starts _
  exact out e (fun h=>near ⟨e.1,List.mem_toFinset.mpr starts,h⟩)

/-- A cold edit preserves even selectors centered far outside the collar. -/
theorem edit_kept (D:Support n)(p:BudgetPoint)(c:Clip)(U V:Fld)
    (out:∀e:Edge (Site n),e.1∉D → U e=V e)(cu:Healthy p.threshold D U)(cv:Healthy p.threshold D V)
    (s:Signed)(z:Site n):
    PathData.kept c p.threshold z (pull s 0 U) ↔ PathData.kept c p.threshold z (pull s 0 V):=by
  unfold PathData.kept
  apply forall_congr';intro x
  rcases cold_plaquette_profile D p U V out cu cv s x with eq|h
  · rw [eq]
  have one:p.threshold≤p.threshold*Real.exp (separation z x.1 / c.relaxation):=
    le_mul_of_one_le_right p.threshold_pos.le (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) c.radius_pos.le))
  exact iff_of_true (h.1.trans one) (h.2.trans one)

def uncutBase (P:PathData G)(c:Clip)(W:Fld)(x:Face (Per n)):ℝ:=
  c.direct*G.price (faceValue W x)+‖P.ell W x‖^2/2

/-- The direct clipped-minus-Wilson plaquette read is constant along every
such edit, even when other plaquettes remain failed in the original field. -/
theorem edited_direct_gap (D:Support n)(p:BudgetPoint)(c:Clip)(U V:Fld)
    (out:∀e:Edge (Site n),e.1∉D → U e=V e)(cu:Healthy p.threshold D U)(cv:Healthy p.threshold D V)
    (s:Signed)(x:Face (Per n)):
    PathData.clipped c p.threshold (G.chord (faceValue (pull s 0 U) x))-c.direct*G.price (faceValue (pull s 0 U) x)=
    PathData.clipped c p.threshold (G.chord (faceValue (pull s 0 V) x))-c.direct*G.price (faceValue (pull s 0 V) x):=by
  rcases cold_plaquette_profile D p U V out cu cv s x with eq|h
  · have paid:G.price (faceValue (pull s 0 U) x)=G.price (faceValue (pull s 0 V) x):=by
      have square:=congrArg (fun t:ℝ=>t^2) eq
      simp only [G.chord_price] at square
      linarith
    rw [eq,paid]
  rw [PathData.clipped,if_pos h.1,PathData.clipped,if_pos h.2,G.chord_price,G.chord_price]
  ring

/-- Exact per-row increment of the whole masked quadratic action minus the
independently filed unclipped action. It vanishes at every retained row. -/
theorem edited_quadratic_gap (D:Support n)(p:BudgetPoint)(c:Clip)(P:PathData G)(U V:Fld)
    (out:∀e:Edge (Site n),e.1∉D → U e=V e)(cu:Healthy p.threshold D U)(cv:Healthy p.threshold D V)
    (s:Signed)(x:Face (Per n)):
    (P.baseTerm c p (pull s 0 U) x-uncutBase P c (pull s 0 U) x)-
      (P.baseTerm c p (pull s 0 V) x-uncutBase P c (pull s 0 V) x)=
    if PathData.kept c p.threshold x.1 (pull s 0 U) then 0
      else (‖P.ell (pull s 0 V) x‖^2-‖P.ell (pull s 0 U) x‖^2)/2:=by
  have direct:=edited_direct_gap D p c U V out cu cv s x
  have same:=edit_kept D p c U V out cu cv s x.1
  by_cases h:PathData.kept c p.threshold x.1 (pull s 0 U)
  · simp only [PathData.baseTerm,uncutBase,if_pos h,if_pos (same.mp h)]
    linarith
  simp only [PathData.baseTerm,uncutBase,if_neg h,if_neg (mt same.mpr h),add_zero]
  linarith

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
