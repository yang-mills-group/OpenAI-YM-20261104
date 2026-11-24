import YM.Integration.WilsonMovingForkReporterHeatedAperture
import YM.Integration.WilsonPhysicalStationThermalRanks

/-! Raw Wilson basis directions and their public reflected returns retain the same occupied tooth counts through every higher filing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterFixedRanks
open Lattice Wilson RG Source Cells Extraction Table
open Further.CorrectedLift (ladder)
open WilsonPhysicalPositionReflectedReturn (ports)
open WilsonPhysicalThermalWickRankSupport (Counted)
open WilsonPhysicalThermalWickRescale (pure)
open WilsonPhysicalThermalWickSky (labels)
open Next.Rank.Configuration
open scoped BigOperators Classical

open Next.Rank Next.Rank.Atlas
open WilsonPhysicalStationThermalRanks (fields probe)
variable {G:Gauge} {C:Family G}

structure Axes (C:Family G) where
  weight : ℕ
  raw : (C.labels.level weight).Index
  dual : (C.labels.level weight).Index
  turn : Signed
  arm : Fin 2
  ordered : ((C.labels.level weight).grades raw).2 ≤ ((C.labels.level weight).grades dual).2
  site : Set (Points 2)
  compact : IsCompact site
  separated : site ⊆ conf 2

def test (a:Axes C) : WilsonMovingForkReporterHeatedAperture.Test C where
  deg := fun _=>a.weight
  height := a.weight
  elevated := fun _=>le_rfl
  raw := fields C (Pi.single a.raw 1) (probe C a.dual a.turn a.arm)
  rank := ![((C.labels.level a.weight).grades a.raw).2,((C.labels.level a.weight).grades a.dual).2]
  pure_rank := (WilsonPhysicalStationThermalRanks.original C a.raw a.dual a.turn a.arm (le_refl a.weight)).1
  capped := (WilsonPhysicalStationThermalRanks.original C a.raw a.dual a.turn a.arm (le_refl a.weight)).2
  increasing := a.ordered
  support := a.site
  compact := a.compact
  clear := a.separated

theorem portable (a:Axes C) {h:ℕ} (fits:a.weight≤h) :
    ∀i,pure ((test a).rank i) (thawKey (labels (test a).raw (fun _=>fits) i)) :=
  (WilsonPhysicalStationThermalRanks.original C a.raw a.dual a.turn a.arm fits).1

end YM.Integration.WilsonMovingForkReporterFixedRanks
end
