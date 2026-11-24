import YM.Integration.WilsonIndependentMatchedTopStencils
import YM.Integration.WilsonIndependentMatchedTopFilm

/-! The complete fitted top uses the same marked amplitudes on the physical
link variables and on the true sample's inversion tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopReceipt
open WilsonCoeffUV WilsonCoeffUV.Shard
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08 Wilson Tree PowerSeries
open Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open XSpace XSpace.Cirrus PhysicalNext.Repeat.Legato FVA2
open WilsonIndependentMatchedNamedPair (sectionAt placed)
open WilsonIndependentMatchedTopFilm (dose word)
open scoped BigOperators Topology Classical
variable {G:Gauge}(R:Run G)(W:Initialize G)(Y:Cirrus.Sample 2)
variable {D d k u e:ℕ}{H:Hol G}{w:d<D}{v:Rails d k u e}{E W₀ K U:Credit}
local notation "F" => R.family.labels.level d

def realDose (b:Volume D)(c:Verse F)(s:Alma F) : PowerSeries ℝ :=
  c s * PowerSeries.C (jewelBloom w s b)

theorem dose_eq (b:Volume D)(c:Verse F)(s:Alma F) :
    TaylorWick.into (realDose R (w:=w) b c s) = dose R w c b s := by
  simp only [realDose,dose,TaylorWick.into,map_mul,PowerSeries.map_C]
  rfl

/-- The exact common numerical dose on the actually funded group stencil at
this same layout. Both the field series and its tree print use every axis. -/
theorem original (survey:Bool)(L:CutsP H (sectionAt R W survey d) w v E W₀ K U)
    (top:L.N=L.ceilC)(i:Fin 2)(b:Volume D) :
    let M:=Shrine L.Ntop L.tileP
    X^WilsonPositionProgramMasterBirth.rank R (d:=d)*flash (jot b (M.1 Y.F.p.side)) =
      ∑ s,X^(WilsonPositionProgramMasterBirth.rank R (d:=d)-valence F s) *
        Blue.soil (realDose R (w:=w) b L.tileP s) *
        jet (fun a=>placed R W Y survey d (Y.layout i) (sheet F s)
          (translate (-(chartV Y i)) (mantle a))) := by
  have head :
      X^WilsonPositionProgramMasterBirth.rank R (d:=d)*flash (jot b ((Shrine L.Ntop L.tileP).1 Y.F.p.side)) =
        ∑ s,X^(WilsonPositionProgramMasterBirth.rank R (d:=d)-valence F s) *
          Blue.soil (L.tileP s) *
          (jewelBloom w s b • jet (Plies (sectionAt R W survey d) (sheet F s) Y.F.p.side)) := by
    cases survey with
    | false => exact WilsonIndependentMatchedTopStencils.original R L top _ b
    | true => exact WilsonIndependentMatchedTopStencils.survey R W L top _ b
  dsimp only
  rw [head]
  refine Finset.sum_congr rfl (fun s _=>?_ )
  rw [←WilsonIndependentMatchedTopFilm.recentered,realDose,map_mul]
  simp only [Blue.soil,PowerSeries.map_C,Algebra.smul_def]
  have scalar (t:ℝ) : algebraMap ℝ (Ink (Woods G Y.F.p.side)) t = PowerSeries.C (MvPolynomial.C t) := by
    rw [IsScalarTower.algebraMap_apply ℝ (POL (Woods G Y.F.p.side)) (Ink (Woods G Y.F.p.side)), MvPolynomial.algebraMap_eq]
    rfl
  rw [scalar]
  ring

end YM.Integration.WilsonIndependentMatchedTopReceipt
