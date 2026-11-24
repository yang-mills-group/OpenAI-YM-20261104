import YM.Integration.WilsonInvariantActionRegisteredHearing
import YM.Integration.OriginalMarkedRunAction

/-! The genuine old hard insertion is unchanged by the premium cut in the
regular Wilson action. Every complete compatible signed forest is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesVacuumKept
open Function Filter Finset MeasureTheory Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato WilsonInvariantActionRegisteredHearing
open private forced_receipt charges_receipt from YM.Integration.OriginalMarkedRunAction
open scoped Classical BigOperators Topology
variable {G:Gauge} {n:Side}

def restricted (P:Rep G n) (w:Finset ℕ→ Config G n→ℝ) (U:Config G n):ℝ:=
  ∑' b,w b U*P.activities.gasOccurrence P.p b U

def normalized (P:Rep G n) (w:Finset ℕ→ Config G n→ℝ) (U:Config G n):ℝ:=
  Real.exp (P.exponent U)*restricted P w U/P.eval U

theorem ratio (P:Rep G n) (w:Finset ℕ→ Config G n→ℝ) (U:Config G n):
    normalized P w U=restricted P w U/P.activities.gas P.p U:=by
  unfold normalized Rep.eval
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem same (P Q:Rep G n) (hp:P.p=Q.p) (hf:P.activities.forced=Q.activities.forced)
    (hk:P.activities.K=Q.activities.K) (w:Finset ℕ→ Config G n→ℝ) (U:Config G n):
    normalized P w U=normalized Q w U:=by
  have identical (b:Finset ℕ):P.activities.gasOccurrence P.p b U=Q.activities.gasOccurrence Q.p b U:=by
    unfold Activities.gasOccurrence Activities.admissible
    rw [hp,hf,hk]
  simp only [ratio,restricted,Activities.gas,identical]

variable (R:Run G) {N per m:ℕ}
local notation "current" => R.family.path.rep N per m
local notation "kept" h:max d:max => OriginalMarkedRunAction.approximation R (p:=per) h d

theorem physical (live:m<N) (d:ℕ) (w:Finset ℕ→ Config G (R.family.side m per)→ℝ)
    (U:Config G (R.family.side m per)):
    normalized (kept live d) w U=normalized current w U:=by
  let S:=ActualRunSpring.selected R N per m live
  apply same _ _ _ (forced_receipt R live S d) (charges_receipt R live S d)
  change (S.spring.result S.point.val).p=(current).p
  rw [←S.coarse]

def owner (i:ℕ) (b:Finset ℕ) :ℝ:=if i∈b then 1 else 0

theorem marked (P:Rep G n) (i:ℕ) (U:Config G n):
    restricted P (fun b _=>owner i b) U=occurrence P i U:=by
  unfold restricted occurrence
  apply tsum_congr
  intro b
  by_cases h:i∈b <;> simp [owner,h]

/-- Both held and fine fields are the real submitted ones. The charge refers
to the same numbered hard activity and all its compatible companions. -/
theorem hearing (original:m+1<N) (d i:ℕ) (V:Config G (R.family.side m per))
    (U:Config G (R.family.side (m+1) per)):
    (score R original (hard R original i)).val (V,U)=
      normalized (OriginalMarkedRunAction.approximation R (p:=per) original d)
        (fun b _=>owner i b) U:=by
  rw [physical,normalized]
  change Real.exp ((R.family.path.rep N per (m+1)).exponent U)*occurrence (R.family.path.rep N per (m+1)) i U/(R.family.path.rep N per (m+1)).eval U=_
  exact congrArg (fun v:ℝ=>Real.exp ((R.family.path.rep N per (m+1)).exponent U)*v/(R.family.path.rep N per (m+1)).eval U) (marked (R.family.path.rep N per (m+1)) i U).symm

end YM.Integration.WilsonMatrixTicketLanesVacuumKept
