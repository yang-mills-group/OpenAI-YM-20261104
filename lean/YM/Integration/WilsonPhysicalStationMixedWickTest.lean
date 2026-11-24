import YM.Integration.WilsonMovingForkReporterHeatedAperture
import YM.Integration.WilsonPhysicalStationThermalRanks
import YM.Integration.WilsonOriginalBlissMixedGram

/-! The Wilson source and the earlier reflected probe may have distinct engineering horizons.
The deposited colours and the free comparison retain those original grades at both sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickTest
open Function Set Filter Lattice Wilson RG Source Cells Further.CorrectedLift
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West Next.Rank.Atlas Next.Rank.Configuration
open Perch Glyph Marker Exponential Trace.Terrace
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationThermalRanks (probe)
open scoped Classical BigOperators Topology
variable {G:Gauge}(C:Family G){l r:ℕ}

def votes (x:C.label l)(z:(standard C).Field r):(i:Fin 2)→C.label (grades l r i):=
  Fin.cons (α:=fun i=>C.label (grades l r i)) x (fun _=>ladder C r z)

def fields (x:C.label l)(z:(standard C).Field r):(i:Fin 2)→(standard C).Field (grades l r i):=
  Fin.cons (α:=fun i=>(standard C).Field (grades l r i)) ((standard C).project l x) (fun _=>z)

def reference (x:C.label l)(z:(standard C).Field r)(y:Points 2):ℂ:=
  (standard C).classMoment (standard C) (grades l r) y (fields C x z)

theorem reads (x:C.label l)(z:(standard C).Field r)(y:Points 2):
    (standard C).useAt (standard C) y (jointX (d0:=grades l r) (votes C x z))=reference C x z y:=by
  let T:=(standard C).classMoment (standard C) (grades l r) y
  apply congrArg (fun v=>T v)
  funext i
  fin_cases i
  · rfl
  · exact ladder_reads (C:=C) z

def test (l r:ℕ)(a:(C.labels.level l).Index)(b:(C.labels.level r).Index)(s:Signed)(side:Fin 2)
    (increasing:((C.labels.level l).grades a).2 ≤ ((C.labels.level r).grades b).2)
    (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2):WilsonMovingForkReporterHeatedAperture.Test C where
  deg:=grades l r
  height:=max l r
  elevated:=by intro i; fin_cases i
               · exact le_max_left _ _
               · exact le_max_right _ _
  raw:=votes C (Pi.single a 1) (probe C b s side)
  rank:=![((C.labels.level l).grades a).2,((C.labels.level r).grades b).2]
  pure_rank:=by
    intro i
    fin_cases i
    · exact WilsonPhysicalThermalWickRankSupport.polynomial _ _ _ (WilsonPhysicalThermalWickRankSupport.axis _ a) (le_max_left _ _)
    · exact WilsonPhysicalThermalWickRankSupport.polynomial _ _ _ (WilsonPhysicalThermalWickProbe.original C b s side) (le_max_right _ _)
  capped:=by
    intro i
    fin_cases i
    · exact (WilsonPhysicalThermalWickRankBound.original _ a).trans (le_max_left _ _)
    · exact (WilsonPhysicalThermalWickRankBound.original _ b).trans (le_max_right _ _)
  increasing:=increasing
  support:=K
  compact:=compact
  clear:=clear

end YM.Integration.WilsonPhysicalStationMixedWickTest
end
