import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseLeading
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true


open scoped Matrix

variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
structure Survey (C:Family G) where
  guests:ℕ
  earlier:Fin guests→(Bel C.book).Tag
  spot:Points (guests+1)
  separate:spot∈conf (guests+1)

def dims (P:Survey C):Caps (P.guests+1):=Fin.cons 4 (fun i=>(P.earlier i).1)
def fixed (P:Survey C):(i:Fin (P.guests+1))→(Bel C.book).Field (dims P i):=
  Fin.cons 0 (fun i=>(P.earlier i).2)
def seats (P:Survey C)(u:(Bel C.book).Field 4):(i:Fin (P.guests+1))→(Bel C.book).Field (dims P i):=
  Function.update (fixed P) 0 u
def tickets (P:Survey C)(u:(Bel C.book).Field 4):Fin (P.guests+1)→(Bel C.book).Tag:=
  fun i=>⟨dims P i,seats P u i⟩

def free (P:Survey C):(Bel C.book).Field 4→ₗ[ℂ]ℂ:=
  ((Bel C.book).classMoment (Bel C.book) (dims P) P.spot).toLinearMap (fixed P) 0

def raw (P:Survey C)(X:Scaling S)(k:ℕ):S.Field 4→ₗ[ℂ]ℂ:=
  (S.classMoment S (dims P) (X.r k • P.spot)).toLinearMap (fun i=>X.U k (dims P i) (fixed P i)) 0

def mean (P:Survey C)(X:Scaling S)(k:ℕ):(Bel C.book).Field 4→ₗ[ℂ]ℂ:=
  (raw P X k).comp (X.U k 4).toLinearMap

def physical (F:Final C f S)(X:Scaling S)(k:ℕ)(a b:Axis):S.Field 4:=
  ((X.r k^4:ℝ):ℂ) • F.sector.energy a b

def born (F:Final C f S)(X:Scaling S)(k:ℕ)(a b:Axis):(Bel C.book).Field 4:=
  (X.U k 4).symm (physical F X k a b)

theorem reader (F:Final C f S)(X:Scaling S)(P:Survey C)(u:(Bel C.book).Field 4)(k:ℕ):
    measured F none (X.U k) (seats P u) (X.r k) P.spot=mean P X k u:=by
  change (S.classMoment S (dims P) (X.r k • P.spot)) (fun i=>X.U k (dims P i) (seats P u i))=
    (S.classMoment S (dims P) (X.r k • P.spot)) (Function.update (fun i=>X.U k (dims P i) (fixed P i)) 0 (X.U k 4 u))
  congr 1
  funext i
  by_cases primary:i=0
  · subst i
    simp [seats,dims]
    rfl
  · simp [seats,Function.update_of_ne primary]

theorem freeRead (P:Survey C)(u:(Bel C.book).Field 4):WickGoal (seats P u) P.spot=free P u:=rfl

theorem observed (F:Final C f S)(X:Scaling S)(P:Survey C)(k:ℕ)(a b:Axis):
    Ward.disc (Pert.scaledPhysical X F.sector.energy k (tickets P 0) (fun i=>decide (i=0)) (fun _=>(a,b)))
      (X.r k • P.spot)=raw P X k (physical F X k a b):=by
  have issued: Pert.scaledPhysical X F.sector.energy k (tickets P 0) (fun i=>decide (i=0)) (fun _=>(a,b))=
      (fun i=>⟨dims P i,(Function.update (fun i=>X.U k (dims P i) (fixed P i)) 0 (physical F X k a b)) i⟩):=by
    funext i
    by_cases home:i=0
    · subst i
      simp [Pert.scaledPhysical,physical,dims]
      rfl
    · simp [Pert.scaledPhysical,tickets,seats,home]
      rfl
  rw [issued]
  rfl

theorem underlying (P:Survey C)(a b:Axis):
    Ward.disc (Pert.freeWithStress C.labels (tickets P 0) (fun i=>decide (i=0)) (fun _=>(a,b))) P.spot=
      free P (Pert.freeStress C.labels a b):=by
  have issued:Pert.freeWithStress C.labels (tickets P 0) (fun i=>decide (i=0)) (fun _=>(a,b))=
      tickets P (Pert.freeStress C.labels a b):=by
    funext i
    by_cases home:i=0
    · subst i
      simp [Pert.freeWithStress,tickets,seats,dims]
      rfl
    · simp [Pert.freeWithStress,tickets,seats,home]
  rw [issued]
  rfl

theorem original {I:Type*}[Fintype I][DecidableEq I](B:Module.Basis I ℂ ((Bel C.book).Field 4))(rows:I→Survey C)
    (F:Final C f S)(X:Scaling S)(k:ℕ)(a b:Axis):
    (fun i j=>mean (rows i) X k (B j)) *ᵥ (fun j=>B.repr (born F X k a b) j)=
      (fun i=>raw (rows i) X k (physical F X k a b)):=by
  funext i
  have paid:=congrArg (mean (rows i) X k) (B.sum_repr (born F X k a b))
  simp only [map_sum,map_smul,smul_eq_mul] at paid
  change (∑j,mean (rows i) X k (B j)*B.repr (born F X k a b) j)=_
  calc
    _ = ∑j,B.repr (born F X k a b) j*mean (rows i) X k (B j):=by apply Finset.sum_congr rfl;intro j _;ring
    _ = mean (rows i) X k (born F X k a b):=paid
    _ = _:=by simp [mean,born]


end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows
end
