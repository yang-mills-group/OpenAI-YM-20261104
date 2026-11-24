import YM.Integration.WilsonPhysicalActualWeakCylinders
import YM.Integration.WilsonOriginalConditionalPhaseSum

/-! Exact elementary readings of a booked physical face at its real sites. Only its
occupied arms are expanded. Its finite restart is evaluated on the original N vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalActualWeakFaces
open Function Filter Finset MeasureTheory Lattice RG Wilson Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalActualWeakNames (name coefficient seed)
open WilsonPhysicalActualWeakCylinders (product amount)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonMovingForkHeterogeneousCut (Filed)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
  {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T n:ℕ}
local notation "C" => R.family
variable {ρ:Fin n→ℝ}(books:(i:Fin n)→Book F (l:=l) H arch D T (ρ i))
  (d:Fin n→Fin (D+1))(v:(i:Fin n)→(Bel R.family.book).Field (d i))(turn:Fin n→Motion)
  (s:(Stock.census (Fin n)).Mode)

abbrev Menu:Type:=(i:↥s.val)→((C).labels.level (d i)).Index

def phase (e:Menu (R:=R) d s):ℂ:=
  amount F J Z (fun i:↥s.val=>books i) (fun i:↥s.val=>d i) (fun i:↥s.val=>v i) (fun i:↥s.val=>turn i) e

def branch (e:Menu (R:=R) d s)(N p:ℕ)(i:Fin n):(C).label (d i):=
  if hi:i∈s.val then seed F (d i) (books i) (e ⟨i,hi⟩) N p else name F J Z (d i) (books i) (v i) N p

def names (N p:ℕ)(i:Fin n):(C).label (d i):=name F J Z (d i) (books i) (v i) N p

private theorem slice {N p j:ℕ}(o:Fin n→Site ((C).side j p))(Y:∀i,(C).label (d i)):
    physical R (fun i=>(d i).val) (N:=N) Y turn o s=
      product (fun i:↥s.val=>d i) (fun i:↥s.val=>turn i) N p (fun i:↥s.val=>anchorAt R (o i) N) (fun i:↥s.val=>Y i):=by
  funext U
  exact (Finset.prod_coe_sort s.val (fun i=>(C).O N p (displayed R (d i) (Y i) (turn i)) (anchorAt R (o i) N) U)).symm

private theorem elementary (e:Menu (R:=R) d s){N p j:ℕ}(o:Fin n→Site ((C).side j p)):
    physical R (fun i=>(d i).val) (N:=N) (branch F J Z books d v s e N p) turn o s=
      product (fun i:↥s.val=>d i) (fun i:↥s.val=>turn i) N p (fun i:↥s.val=>anchorAt R (o i) N)
        (fun i:↥s.val=>seed F (d i) (books i) (e i) N p):=by
  rw [slice]
  have h:(fun i:↥s.val=>branch F J Z books d v s e N p i)=(fun i:↥s.val=>seed F (d i) (books i) (e i) N p):=by
    funext i
    simp only [branch,dif_pos i.property]
  rw [h]

/-- Full or proper ordinary face before either original regulator. -/
theorem original {N p j:ℕ}(o:Fin n→Site ((C).side j p)):
    (C).omega N p (physical R (fun i=>(d i).val) (names F J Z books d v N p) turn o s)=
      ∑e:Menu (R:=R) d s,phase F J Z books d v turn s e *
        (C).omega N p (physical R (fun i=>(d i).val) (branch F J Z books d v s e N p) turn o s):=by
  rw [slice]
  simp_rw [elementary F J Z books d v turn s]
  convert! WilsonPhysicalActualWeakCylinders.original F J Z (fun i:↥s.val=>books i) (fun i:↥s.val=>d i)
    (fun i:↥s.val=>v i) (fun i:↥s.val=>turn i) N p (fun i:↥s.val=>anchorAt R (o i) N) using 6

/-- Every restart comes from its actual filed elementary group; deposition uses the one
original N posterior at the earlier stop and keeps its full ordinary face. -/
theorem hearing {N p j K u:ℕ}(fk:j≤K)(road:u≤K)(o:Fin n→Site ((C).side j p))(W:Config G ((C).side u p))
    (file:Menu (R:=R) d s→Filed R (fun i=>(d i).val) K)(Δ:ℝ)
    (regular:∀e:Menu (R:=R) d s,Integrable (fun U=>((C).path.rep N p K).eval U •
      submitted R _ (N:=N) (file e) fk (branch F J Z books d v s e N p) turn o s U) (prior G _))
    (quote:∀e:Menu (R:=R) d s,‖(C).omega N p
      (physical R (fun i=>(d i).val) (branch F J Z books d v s e N p) turn o s)-
        actualTransport (C) (N:=N) (submitted R _ (N:=N) (file e) fk (branch F J Z books d v s e N p) turn o s) road W‖≤Δ):
    ‖(C).omega N p (physical R (fun i=>(d i).val) (names F J Z books d v N p) turn o s)-
      actualTransport (C) (N:=N) (fun U=>∑e:Menu (R:=R) d s,phase F J Z books d v turn s e*
        submitted R _ (N:=N) (file e) fk (branch F J Z books d v s e N p) turn o s U) road W‖≤
      (∏i:↥s.val,∑g,‖coefficient F J Z (d i) (books i) (v i) g‖)*Δ:=by
  let a:=phase F J Z books d v turn s
  let printed:=fun (e:Menu (R:=R) d s)=>submitted R _ (N:=N) (file e) fk (branch F J Z books d v s e N p) turn o s
  obtain ⟨_,linear⟩:=WilsonOriginalConditionalPhaseSum.original R Finset.univ a printed regular road W
  rw [linear,slice]
  convert! WilsonPhysicalActualWeakCylinders.charged F J Z (fun i:↥s.val=>books i) (fun i:↥s.val=>d i)
    (fun i:↥s.val=>v i) (fun i:↥s.val=>turn i) N p (fun i:↥s.val=>anchorAt R (o i) N)
      (fun e=>actualTransport (C) (N:=N) (printed e) road W) Δ
      (fun e=>by simpa only [elementary F J Z books d v turn s e] using quote e) using 6

end YM.Integration.WilsonPhysicalActualWeakFaces
