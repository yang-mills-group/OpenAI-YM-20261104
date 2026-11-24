import YM.Integration.WilsonPhysicalActualMixedFaces
import YM.Integration.WilsonOriginalFiniteRosterTrialRead

/-! Gross and signed earnings for the actual filed public ordinary faces on the
N-inherited posterior. Each primitive uses its own restored K vector and all names
are retained in one numerator on the measured original course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalOccupiedPosterior
open Function Filter Finset MeasureTheory Lattice RG Wilson Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPhysicalActualMixedFaces (Menu branch names phase)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonOriginalMicroscopicGuardedWallet (loss)
open scoped Classical BigOperators
section Gross
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

theorem affordable {n:ℕ}(d:Fin n→ℕ){N p j K:ℕ}(live:K≤N)(file:Filed R d K)(fk:j≤K)
    (Y:∀i,(C).label (d i))(turn:Fin n→Motion)(o:Fin n→Site ((C).side j p))(s:(Stock.census (Fin n)).Mode):
    let gross:=∏i∈s.val,loss R (d i) K*((C).labels.level (d i)).coeffSize (votes R d (N:=N) (per:=p) file Y turn i)
    let print:=submitted R d (N:=N) file fk Y turn o s
    Integrable (fun U=>((C).path.rep N p K).eval U • print U) (prior G _) ∧
    ∀u (road:u≤K) (W:Config G ((C).side u p)),‖actualTransport (C) (N:=N) print road W‖≤gross:=by
  let v:=votes R d (N:=N) (per:=p) file Y turn
  let z:=fun i=>((C).S.toDepth fk p).embed (o i)
  have wage:=fun i=>WilsonOriginalFiniteRosterTrialRead.arm R (d i) N p K live (z i) (v i)
  have m:Measurable (submitted R d (N:=N) file fk Y turn o s):=by
    change Measurable (fun U=>∏i∈s.val,uncut R (d i) N p K (z i) (v i) U)
    exact Finset.measurable_prod _ fun i _=>(wage i).1
  have paid (U):‖submitted R d (N:=N) file fk Y turn o s U‖≤
      ∏i∈s.val,loss R (d i) K*((C).labels.level (d i)).coeffSize (v i):=by
    change ‖∏i∈s.val,uncut R (d i) N p K (z i) (v i) U‖≤_
    rw [norm_prod]
    exact prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>(wage i).2 U)
  have int:=actualTransport_weighted_integrable (C) R.makes live m.aestronglyMeasurable paid (le_refl K)
  rw [actualTransport_base (C) R.makes live] at int
  exact ⟨int,fun _ road W=>actualTransport_norm_le (C) R.makes live paid road W⟩

end Gross

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
  {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T n:ℕ}
local notation "C" => R.family
variable {ρ:Fin n→ℝ}(books:(i:Fin n)→Book F (l:=l) H arch D T (ρ i))
  (d:Fin n→Fin (D+1))(v:(i:Fin n)→(Bel R.family.book).Field (d i))(weak:Fin n→Bool)(turn:Fin n→Motion)
  (s:(Stock.census (Fin n)).Mode)

theorem original {N p j K u:ℕ}(fk:j≤K)(live:K≤N)(road:u≤K)(o:Fin n→Site ((C).side j p))(W:Config G ((C).side u p))
    (file:Menu (R:=R) d weak s→Filed R (fun i=>(d i).val) K)(debit:Menu (R:=R) d weak s→ℝ)
    (quote:∀e:Menu (R:=R) d weak s,‖(C).omega N p
      (physical R (fun i=>(d i).val) (branch F J Z books d v weak s e N p) turn o s)-
        actualTransport (C) (N:=N) (submitted R _ (N:=N) (file e) fk (branch F J Z books d v weak s e N p) turn o s) road W‖≤debit e):
    ‖(C).omega N p (physical R (fun i=>(d i).val) (names F J Z books d v weak N p) turn o s)-
      actualTransport (C) (N:=N) (fun U=>∑e:Menu (R:=R) d weak s,phase F J Z books d v weak turn s e*
        submitted R _ (N:=N) (file e) fk (branch F J Z books d v weak s e N p) turn o s U) road W‖≤
      ∑e:Menu (R:=R) d weak s,‖phase F J Z books d v weak turn s e‖*debit e:=
  WilsonPhysicalActualMixedFaces.hearing F J Z books d v weak turn s fk road o W file debit
    (fun e=>(affordable R _ live (file e) fk (branch F J Z books d v weak s e N p) turn o s).1) quote

end YM.Integration.WilsonPhysicalOccupiedPosterior
