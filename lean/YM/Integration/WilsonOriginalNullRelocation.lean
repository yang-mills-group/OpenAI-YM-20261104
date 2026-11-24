import YM.PECompat4984.Donor.Tickets
import YM.Extra.SOURCE_HISTORIES.Offsets
import YM.Integration.WilsonOriginalNullCalibrated

/-! Relocating the complete physical cash on the native permutation of all
forced owners preserves its measured held-link germ, including its unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullRelocation
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Next.Foundations Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical BigOperators

variable {G:Gauge} {n:Side} {d:ℕ} (F:Frame G d) (A:Hol G)

theorem mark (o t:Site n) (f:Config G n→ℂ) :
    label A (o+t) (f∘translate t) d=label A o f d := by
  let chooseJet (p : Label G d→Prop) := if h:∃ a,p a then h.choose else 0
  change chooseJet (fun a=>JetTest A (o+t) a (f∘translate t)) =
    chooseJet (fun a=>JetTest A o a f)
  apply congrArg chooseJet
  funext q
  simp only [JetTest,comp_apply,Drift.test_translate]

theorem page (θ:ℝ) (o t:Site n) {P:Rep G n} (moved:P.activities.Moves 1 t)
    (q:Coefficient F n) :
    projection F A θ (o+t) (Drift.stamp t moved q)=projection F A θ o q := by
  change q.x+(∑' i,vector F A θ (o+t) (q.regular i∘translate t))=
    q.x+∑' i,vector F A θ o (q.regular i)
  apply congrArg (q.x+·)
  apply tsum_congr
  intro i
  exact congrArg (fun l=>F.scaled θ (F.coords l)) (mark A o t (q.regular i))

theorem center (o t:Site n) {P:Rep G n} (moved:P.activities.Moves 1 t) (α:F.Coeff) :
    Drift.stamp t moved (primary o α)=primary (o+t) α := by
  simp [Drift.stamp,Extra.Histories.primary,Drift.relocated,Function.comp_def]
  funext i U;rfl

variable (C:Family G) (h:C.Makes) (d N p i:ℕ)

theorem registered (live:i ≤ N) (o t:Site (C.side i p)) (q:Coefficient (C.labels.level d) (C.side i p)) :
    let P:=C.path.rep N p i
    let move:=Tour.placard C h N p live t
    (Drift.stamp t move q).density (o+t) (C.localSection d) P=
      (fun U=>q.density o (C.localSection d) P (translate t U)) := by
  intro P move
  have eq (U:Config G (C.side i p)):P.eval U=P.eval (translate t U):=by
    have hp:=vac_pull C.path N p i h.wilson live 1 t U
    rw [Lattice.pull_one] at hp
    exact Complex.ofReal_injective hp.symm
  funext U
  exact Drift.stamped t move eq (fun U=>(Tour.bright C.path h.wilson N p i live U).ne')
    q (C.localSection d) o U

end YM.Integration.WilsonOriginalNullRelocation
