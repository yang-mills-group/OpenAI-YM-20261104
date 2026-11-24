import YM.Integration.WilsonPhysicalFiledSlotExpansion
import YM.Integration.WilsonPhysicalOccupiedPosterior

/-! Reassemble all signed elementary axes into the single true filed public K word
on each occupied ordinary face. The original normalized reading uses N's prior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalFiledPublicRecomposition
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow RG16 RG16.Literal
open Climb OPE Overlay Bid Push.GridApprox RG17 PhysMS EveryPhase OPE.Orbits OPE.Log MS MS.Land FVA2 FVA2.Register
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalActualMixedMenus (Port weight source multiplier)
open WilsonPhysicalActualMixedFaces (Menu phase branch names)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPhysicalFiledSlotExpansion (reading)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
  {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T n:ℕ}
local notation "C" => R.family
variable {ρ:Fin n→ℝ}(books:(i:Fin n)→Book F (l:=l) H arch D T (ρ i))
  (d:Fin n→Fin (D+1))(v:(i:Fin n)→(Bel R.family.book).Field (d i))(weak:Fin n→Bool)(turn:Fin n→Motion)
  (s:(Stock.census (Fin n)).Mode)

theorem original {N per f₀ K:ℕ}(fk:f₀≤K)(o:Fin n→Site ((C).side f₀ per))(file:Filed R (fun i=>(d i).val) K)
    (eligible:∀i∈s.val,(C).ref (d i)≤file.station i)(live:∀i∈s.val,file.station i≤N):
    submitted R (fun i=>(d i).val) (N:=N) file fk (names F J Z books d v weak N per) turn o s=
      fun U=>∑e:Menu (R:=R) d weak s,phase F J Z books d v weak turn s e *
        submitted R (fun i=>(d i).val) (N:=N) file fk (branch F J Z books d v weak s e N per) turn o s U:=by
  funext U
  let atSite (i:Fin n):((C).label (d i))→ℂ:=reading R (d i) (file.station i) N per K
    (file.A N per i) (turn i) (((C).S.toDepth fk per).embed (o i)) U
  have represented (Y:∀i,(C).label (d i)):
      submitted R (fun i=>(d i).val) (N:=N) file fk Y turn o s U=∏i:↥s.val,atSite i (Y i):=
    (Finset.prod_coe_sort s.val (fun i=>atSite i (Y i))).symm
  have elementary (e:Menu (R:=R) d weak s):
      submitted R (fun i=>(d i).val) (N:=N) file fk (branch F J Z books d v weak s e N per) turn o s U=
        ∏i:↥s.val,atSite i (source F J Z (d i) (books i) (v i) (weak i) (e i) N per):=by
    rw [represented]
    apply Finset.prod_congr rfl
    intro i _
    simp only [branch,dif_pos i.property]
  rw [represented]
  simp_rw [elementary]
  have slot (i:↥s.val):atSite i (names F J Z books d v weak N per i)=
      ∑e:Port R (d i) (weak i),Motion.scalar (turn i) (weight F J Z (d i) (books i) (v i) (weak i) e) *
        atSite i (source F J Z (d i) (books i) (v i) (weak i) e N per):=
    WilsonPhysicalFiledSlotExpansion.original R F J Z (books i) (d i) (v i) (weak i)
      (file.station i) N per K (eligible i i.property) (live i i.property) (file.A N per i) (turn i) _ U
  simp_rw [slot,Fintype.prod_sum,Finset.prod_mul_distrib]
  rfl

theorem earned {N per f₀ K u:ℕ}(fk:f₀≤K)(cut:K≤N)(road:u≤K)(o:Fin n→Site ((C).side f₀ per))(W:Config G ((C).side u per))
    (file:Filed R (fun i=>(d i).val) K)(eligible:∀i∈s.val,(C).ref (d i)≤file.station i)
    (live:∀i∈s.val,file.station i≤N)(debit:Menu (R:=R) d weak s→ℝ)
    (quote:∀e:Menu (R:=R) d weak s,‖(C).omega N per
        (physical R (fun i=>(d i).val) (branch F J Z books d v weak s e N per) turn o s)-
      actualTransport (C) (N:=N) (submitted R (fun i=>(d i).val) (N:=N) file fk
        (branch F J Z books d v weak s e N per) turn o s) road W‖≤debit e):
    ‖(C).omega N per (physical R (fun i=>(d i).val) (names F J Z books d v weak N per) turn o s)-
      actualTransport (C) (N:=N) (submitted R (fun i=>(d i).val) (N:=N) file fk (names F J Z books d v weak N per) turn o s)
        road W‖≤∑e:Menu (R:=R) d weak s,‖phase F J Z books d v weak turn s e‖*debit e:=by
  rw [original F J Z books d v weak turn s fk o file eligible live]
  exact WilsonPhysicalOccupiedPosterior.original F J Z books d v weak turn s fk cut road o W (fun _=>file) debit quote

/-- The issued physical book and original cutoff file discharge both station
conditions on every subset, before any choice of group field at the receiver. -/
theorem booked {N per f₀ K:ℕ}(fk:f₀≤K)(cut:K≤N)(o:Fin n→Site ((C).side f₀ per))
    (file:Filed R (fun i=>(d i).val) K)
    (home:file.station=fun i=>WilsonReflectedPublicStationFare.station F ((books i).rows (d i)) (weak i)):
    submitted R (fun i=>(d i).val) (N:=N) file fk (names F J Z books d v weak N per) turn o s=
      fun U=>∑e:Menu (R:=R) d weak s,phase F J Z books d v weak turn s e *
        submitted R (fun i=>(d i).val) (N:=N) file fk (branch F J Z books d v weak s e N per) turn o s U:=by
  apply original F J Z books d v weak turn s fk o file _ (fun i _=>(file.before i).trans cut)
  intro i _
  rw [home]
  exact (WilsonReflectedPublicStationFare.original F ((books i).rows (d i)) (books i).checked
    (weak i) (0:S.Field (d i))).1

end YM.Integration.WilsonPhysicalFiledPublicRecomposition
