import YM.Integration.WilsonPositionProgramTrialPublicCellPhase

/-! Integrate the original punctual signed readings on the measured physical cells before either ultraviolet regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellIntegral
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

private theorem pull_test (R:Run G){r:ℝ}(rp:0<r)(K:ℕ)(z:Fin n → Cover)(Φ:Test n):
    Integrable (fun ξ=>Φ (pull (R:=R) r K z ξ)):=by
  let scale:=R.family.S.a K/r
  let H:Points n≃ₜPoints n:=(Homeomorph.smul (α:=Points n) (Units.mk0 scale (div_pos (R.family.S.a_pos K) rp).ne')).trans
    (Homeomorph.addLeft (WilsonViewerAffineCells.anchor (R:=R) r K z))
  exact (Φ.continuous.comp H.continuous).integrable_of_hasCompactSupport (Φ.hasCompactSupport.comp_homeomorph H)

variable (R:Run G)(W:Initialize G)(D d:(Fin (a+1))→ℕ)(cut:∀i,d i<D i)
variable (m K N host c:ℕ)(hc:host≤c)(cK:c≤K)(KN:K≤N)(simple:G.Simple)(ratio:LocalRatio R.metals.O)
variable (S:Finset (Fin (a+1)))[Nonempty S](idx:Fin n≃S)
variable (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
variable (φ:(Fin (a+1))→ℂ→L[ℝ]ℝ)(T:(i:(Fin (a+1)))→Rarity (D i))(y:ℝ)(o:CellR){r:ℝ}(rp:0<r)
variable (Φ:Test n)(product:∀t:Points n,Φ t=((∏i,(T (idx i)).ψ.val (fun e=>t i e):ℝ):ℂ))
variable (read:Era G ℝ →ₗ[ℝ] ℂ)

include W cut hc cK KN simple ratio product in
theorem samples (nodes:Finset (Fin n → Cover))
    (contains:∀t:Points n,Φ t≠0→Extraction.address (R.family.S.a K) (r • t)∈nodes)
    (ξ:Points n)(live:ξ∈cube 1 1 (0:Fin n → Cover)):
    let x:=paceT R.family.S m K
    let σ:=r/R.family.S.a m
    let tests:=moved D S idx T x y σ (div_pos rp (R.family.S.a_pos m)) o ξ
    (∑z∈nodes,((R.family.S.a K/r)^(4*n) • Φ (pull (R:=R) r K z ξ))*
       read (node R D d N K c host S fill v φ (layout S idx z)))=
       (∏i:S,x^(d i)) • read (logged R D d m K N host c S fill v φ tests y o):=by
  intro x σ tests
  let U:=nodes.map (layout S idx).toEmbedding
  have room (z:S→ Cover)(w:WilsonPositionProgramTrialPublicCellVisits.weight D d S tests x y o z≠0):z∈U:=by
    let v₀:=(layout S idx).symm z
    have lt:0<x:=pace_pos .. 
    have full:Φ (pull (R:=R) r K v₀ ξ)≠0:=by
      intro zero
      have eq:=WilsonPositionProgramTrialPublicCellPhase.measured R D d S idx T rp m K y o v₀ ξ Φ product
      dsimp only at eq
      rw [zero,smul_zero] at eq
      have h: (∏i:S,x^(d i))*WilsonPositionProgramTrialPublicCellVisits.weight D d S tests x y o z=0:=by
        apply Complex.ofReal_eq_zero.mp
        simpa only [v₀,Equiv.apply_symm_apply] using eq
      exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ lt.ne')) w) h
    have hit:Extraction.address (R.family.S.a K) (r • pull (R:=R) r K v₀ ξ)=v₀:=
      (WilsonPositionProgramTrialPublicCellMass.cell R rp K v₀ ξ).mpr live
    have inNodes:=contains _ full
    rw [hit] at inNodes
    exact Finset.mem_map.mpr ⟨v₀,inNodes,(layout S idx).apply_symm_apply z⟩
  rw [←WilsonPositionProgramTrialPublicCellVisits.original R W D d cut N K m c host hc cK KN simple ratio S
    fill v φ tests y o U room,map_sum,Finset.smul_sum,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul,smul_smul,Complex.real_smul]
  exact congrArg (·*read (node R D d N K c host S fill v φ (layout S idx z)))
    (WilsonPositionProgramTrialPublicCellPhase.measured R D d S idx T rp m K y o z ξ Φ product).symm

include W cut hc cK KN simple ratio product in
theorem original :
    let x:=paceT R.family.S m K
    let σ:=r/R.family.S.a m
    Φ.applyTo (fun t=>read (node R D d N K c host S fill v φ
      (layout S idx (Extraction.address (R.family.S.a K) (r • t)))))=
      ∫ξ in cube 1 1 (0:Fin n → Cover),(∏i:S,x^(d i)) • read
        (logged R D d m K N host c S fill v φ
          (moved D S idx T x y σ (div_pos rp (R.family.S.a_pos m)) o ξ) y o):=by
  intro x σ
  obtain ⟨nodes,inNodes⟩:=WilsonMeasuredPublicEntranceCoverCells.finite Φ (R.family.S.a K) r (R.family.S.a_pos K)
  let value (z:Fin n → Cover):=read (node R D d N K c host S fill v φ (layout S idx z))
  let scale:=(R.family.S.a K/r)^(4*n)
  let tile:=cube 1 1 (0:Fin n → Cover)
  have finite (z:Fin n → Cover):IntegrableOn (fun ξ=>scale • Φ (pull (R:=R) r K z ξ)*value z) tile:=by
    exact (((pull_test R rp K z Φ).smul scale).mul_const (value z)).integrableOn
  rw [WilsonMeasuredPublicEntranceCoverCells.tested Φ (R.family.S.a K) r (R.family.S.a_pos K) nodes inNodes value]
  calc
    _=∫ξ in tile,∑z∈nodes,(scale • Φ (pull (R:=R) r K z ξ))*value z:=by
      rw [integral_finsetSum _ (fun z _=>finite z)]
      apply Finset.sum_congr rfl
      intro z _
      rw [WilsonPositionProgramTrialPublicCellMass.original R rp K z Φ,←integral_smul,integral_mul_const]
    _=_:=by
      apply setIntegral_congr_fun (WilsonMeasuredPublicEntranceCoverCells.visible 1 1 one_pos _)
      intro ξ live
      exact samples R W D d cut m K N host c hc cK KN simple ratio S idx fill v φ T y o rp Φ product read
        nodes inNodes ξ live

end YM.Integration.WilsonPositionProgramTrialPublicCellIntegral
end
