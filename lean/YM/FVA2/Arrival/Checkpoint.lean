import YM.FVA2.Arrival.Net
import YM.FVA2.Continuum.Reg
/-!
# Supplier checkpoint (CP3, cost/removal). Simultaneous with the original MS endpoint applications
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Arrival
open MS MS.Local.Physical MS.Tide MS.Tide.PeakT MS.Fleet MS.Orbit MS.Vista MS.Vane MS.Tone MS.Rake MS.Land MS.Dial
open XSpace.Cirrus Press Change Schedule Landing Filter Continuum
variable (G:Gauge) (s:Continuation G) (h:G.Simple)
/-- This chooses a common *unmarked* tuning (in particular the coupling reset from the
literal MS entrance). Use literally either `Tide` version or `Dial` version via ProofStart. Keep
`tuned fee` separate in pre-W and BornFull as described. This has actual realizations and
the `Gate` estimates for any `Uses`, including `Schedule.performance`, which
exhausts each $G^{X}$ sample profile. See `Landing.runs` and `Undo.quotient_rate`.
Position renormalization is a separate comparison. -/
theorem checkpoint3 (dial:Bool) : let A:= Continuation.proofStart h s dial
    TruePlan s.data s.toInitialize A ∧ ∃ M:Land.Prescription (Press.portDeck G), M.team=A.team ∧ Lifetime s.toInitialize s.data M:= by
    intro A; obtain H:= Continuation.plan s h dial; exact ⟨ H,Landing.at_team s.toInitialize s.data h H.taylor ⟩
include h in
-- example concrete choice
lemma installed (dial:Bool) : let x:= Continuum.some G
      let p:= Continuation.proofStart h x dial
      ∃ M:Land.Prescription (Press.portDeck G), M.team=p.team ∧ Lifetime x.toInitialize x.data M:= (checkpoint3 G (Continuum.some G) h dial).2
end YM.FVA2.Arrival
