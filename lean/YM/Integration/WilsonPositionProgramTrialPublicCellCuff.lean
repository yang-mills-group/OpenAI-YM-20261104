import YM.Integration.WilsonPositionProgramTrialPublicCellObserver

/-! The accrued cutoff return tested on the original continuum product profile and its genuine microscopic cells. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellCuff
open Precision Function Finset Lattice Laurent Wilson RG Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.StableStrip WilsonCoeffUV.Power
open RG.Supply Next.Foundations PhysicalNext.Repeat
open WilsonFiniteMarkedHistoryStep
open WilsonOriginalPublicNodalChildSites (digits here)
open WilsonPositionProgramTrialPublicPulse (choices frame sites survey)
open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonPositionProgramTrialPublicGather (gather)
open WilsonPositionProgramTrialPublicOldReturn (portfolio)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramTrialHomeFaces (Filed)
open WilsonMarkedIndependentNormalizedElection (deck)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramTrialAccrued (home)

variable {G:Gauge}{a n:ℕ}
open MeasureTheory Extraction Table
open WilsonPositionProgramTrialPublicCensusReturn (logged)
open WilsonPositionProgramTrialPublicCellVisits (node)
open WilsonPositionProgramTrialPublicCellPhase (layout moved)
open WilsonMeasuredPublicEntranceCoverCells (cube)
open WilsonViewerAffineCells (pull)

open WilsonPositionProgramTrialPublicCellObserver (grade)
open private pull_test from YM.Integration.WilsonPositionProgramTrialPublicCellIntegral
variable (R:Run G)(W:Initialize G)(D d:(Fin (a+1))→ℕ)(cut:∀i,d i<D i)
variable (m K N host c:ℕ)(hc:host≤c)(cK:c≤K)(KN:K≤N)(simple:G.Simple)(ratio:LocalRatio R.metals.O)
variable (S:Finset (Fin (a+1)))[Nonempty S](idx:Fin n≃S)
variable (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
variable (φ:(Fin (a+1))→ℂ→L[ℝ]ℝ)(T:(i:(Fin (a+1)))→Rarity (D i))(y:ℝ)(o:CellR){r:ℝ}(rp:0<r)
variable (Φ:Test n)(product:∀t:Points n,Φ t=((∏i,(T (idx i)).ψ.val (fun e=>t i e):ℝ):ℂ))
variable (read:Era G ℝ →ₗ[ℝ] ℂ)

include W cut hc cK KN simple ratio product in
theorem integrable :
    let x:=paceT R.family.S m K
    let σ:=r/R.family.S.a m
    IntegrableOn (fun ξ=>(∏i:S,x^(d i)) • read (logged R D d m K N host c S fill v φ
      (moved D S idx T x y σ (div_pos rp (R.family.S.a_pos m)) o ξ) y o)) (WilsonPositionProgramTrialPublicCellObserver.tile n):=by
  intro x σ
  obtain ⟨nodes,inNodes⟩:=WilsonMeasuredPublicEntranceCoverCells.finite Φ (R.family.S.a K) r (R.family.S.a_pos K)
  let value (z:Fin n → Cover):=read (node R D d N K c host S fill v φ (layout S idx z))
  let scale:=(R.family.S.a K/r)^(4*n)
  have parts (z:Fin n → Cover):IntegrableOn (fun ξ=>(scale • Φ (pull (R:=R) r K z ξ))*value z) (WilsonPositionProgramTrialPublicCellObserver.tile n):=
    (((pull_test R rp K z Φ).smul scale).mul_const (value z)).integrableOn
  apply (integrable_finsetSum nodes (fun z _=>parts z)).congr
  apply (ae_restrict_iff' (WilsonMeasuredPublicEntranceCoverCells.visible 1 1 one_pos _)).mpr
  exact ae_of_all _ (fun ξ inTile=>WilsonPositionProgramTrialPublicCellIntegral.samples R W D d cut m K N host c
    hc cK KN simple ratio S idx fill v φ T y o rp Φ product read nodes inNodes ξ inTile)

include W cut hc cK KN simple ratio product in
theorem returned (e u q:ℕ)(live:q≤e)(target:Points n→Era G ℝ)(fee:ℝ):
    let x:=paceT R.family.S m K
    let σ:=r/R.family.S.a m
    let amount:=∏i:S,x^(d i)
    let received:=fun ξ=>logged R D d m K N host c S fill v φ
      (moved D S idx T x y σ (div_pos rp (R.family.S.a_pos m)) o ξ) y o
    IntegrableOn (fun ξ=>amount • grade G q (target ξ)) (WilsonPositionProgramTrialPublicCellObserver.tile n) →
    (∀ξ∈WilsonPositionProgramTrialPublicCellObserver.tile n,response e u (received ξ-target ξ) fee) →
    ‖Φ.applyTo (fun t=>grade G q (node R D d N K c host S fill v φ
        (layout S idx (Extraction.address (R.family.S.a K) (r • t)))))-
      ∫ξ in WilsonPositionProgramTrialPublicCellObserver.tile n,amount • grade G q (target ξ)‖≤volume.real (WilsonPositionProgramTrialPublicCellObserver.tile n)*(amount*fee):=by
  intro x σ amount received valid paid
  rw [WilsonPositionProgramTrialPublicCellIntegral.original R W D d cut m K N host c hc cK KN simple ratio
    S idx fill v φ T y o rp Φ product (grade G q)]
  exact WilsonPositionProgramTrialPublicCellObserver.integrated
    (Finset.prod_nonneg (fun i _=>pow_nonneg (div_nonneg (R.family.S.a_pos K).le (R.family.S.a_pos m).le) _)) live
    (integrable R W D d cut m K N host c hc cK KN simple ratio S idx fill v φ T y o rp Φ product (grade G q)) valid paid

end YM.Integration.WilsonPositionProgramTrialPublicCellCuff
end

