import YM.Integration.WilsonThermometerWeakSeparatedStops

/-! The distinct two-cell invoice is invariant under one actual fine shift
of the complete bare pair with its two independently fixed source labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMovedExperiment
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
open Next.Rank.Price Next.Rank.Tapes.West Next.Rank.Station Next.Rank.East
open Further.CorrectedLift MergeProof MergeProof.East MergeProof.Accent
open PhysicalNext.Repeat.Legato YM.Integration.WilsonLimitConstruction YM.Integration.WilsonPositionThermometerStationNorm
open RG12 RG05Readout Native Address Many Records Harvest
open WilsonThermometerOwnOffsetField WilsonThermometerWeakPanelBorn WilsonThermometerSmallPanelRead
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "C" => R.family

private theorem location (S:Schedule) (N p:ℕ) (a:Cover) :
    Cells.location S N N p a=wrap (S.side N p) a:=by
  unfold Cells.location
  rw [dif_pos le_rfl]
  unfold Ratio.embed Schedule.toDepth
  simp only [tsub_self,Schedule.steps]
  rw [show ((1:Side).val:ℕ)=1 from rfl,one_smul,wrap_lift]

theorem original (S:Schedule) : ∃e:ℕ,∀(m N p:ℕ)(r:Fin 2→ℕ)(deep:∀i,m+e+1≤r i)(live:∀i,r i≤N)
    (x:Fin 2 → Cover),
    (∃j:Axis,S.a m≤|S.gridPoint N (x 0) j-S.gridPoint N (x 1) j|) →
    (∀j:Axis,2*(|S.gridPoint N (x 0) j-S.gridPoint N (x 1) j|+S.a m)<(S.side m p).val*S.a m) →
    let T:=center S p (by have h:=deep 0;have h':=live 0;omega:m≤N) 0
    ∃ (v:Site (S.side N p)) (c:Fin 2 → Site (S.side m p)),c 0≠c 1 ∧
      ∀i,wrap (S.side N p) (x i)+v ∈ T.margin (c i) (3*span S (live i) p):=by
  obtain ⟨e,stop⟩:=WilsonThermometerWeakFineStops.original S
  refine ⟨e,?_⟩
  intro m N p r deep live x gap period T
  obtain ⟨t,u,valid,room⟩:=stop m N p r deep live x
  refine ⟨wrap _ t,fun i=>wrap _ (u i),WilsonThermometerWeakSeparatedStops.separated S m N p r x u t valid gap period,?_⟩
  intro i
  simpa only [location,map_add] using room i

theorem shifted {d e N p:ℕ} (X:(C).label d) (Y:(C).label e) (c:ℂ) (o z t:Site ((C).side N p)):
    moment ((C).beta N p) (fun U=>(C).O N p X (o+t) U*(c*(C).O N p Y (z+t) U))=
    moment ((C).beta N p) (fun U=>(C).O N p X o U*(c*(C).O N p Y z U)):=by
  let pair:Config G ((C).side N p)→ℂ:=fun U=>(C).O N p X o U*(c*(C).O N p Y z U)
  have cont:Continuous pair:=((C).continuousO ..).mul (continuous_const.mul ((C).continuousO ..))
  have honest:Integrable pair (law G _ ((C).beta N p)):=cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [←moment_pull ((C).beta N p) 1 t pair honest]
  congr 1
  funext U
  change _=(C).O N p X o (pull 1 t U)*(c*(C).O N p Y z (pull 1 t U))
  rw [pull_one,(C).translation,(C).translation]

end YM.Integration.WilsonThermometerWeakMovedExperiment
end
