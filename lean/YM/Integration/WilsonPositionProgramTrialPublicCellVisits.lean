import YM.Integration.WilsonPositionProgramTrialPublicCensusReturn
import YM.Integration.WilsonPositionProgramTrialPublicSocketFactors

/-! Reindex the native visited cells by physical sites while retaining the complete signed source. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellVisits
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

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]
open WilsonPositionProgramTrialPublicCensusReturn (logged)
open WilsonPositionProgramTrialPublicSpatialSum (held)
open WilsonOriginalPublicNodalPlainSensor (sensor)
open WilsonPositionProgramTrialPublicGather (ear)

def extendSites (S:Finset I)(z:S→ Cover)(i:I):Cover:=if h:i∈S then z ⟨i,h⟩ else 0

def node (R:Run G)(D d:I→ℕ)(N K c host:ℕ)(S:Finset I)
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(z:S→ Cover):Era G ℝ:=
  let L:=R.family.path.levels
  portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ (fun i=>ear (D i) 1)
    L R.metals.O N (digits L K (extendSites S z)) host c K (here L K (extendSites S z) c)

def weight (D d:I→ℕ)(S:Finset I)(T:(i:I)→Rarity (D i))(x y:ℝ)(o:CellR)(z:S→ Cover):ℝ:=
  ∏i:S,sensor (D i) (held (D i) (T i) x y o (d i) (z i))

def location (D:I→ℕ)(S:Finset I)(T:(i:I)→Rarity (D i))(x y:ℝ)(o:CellR):
    choices D T (fun _=>x) y (fun _=>o) S ↪ (S→ Cover) where
  toFun z:=fun i=>(z i).val
  inj' a b hab:=by funext i;exact Subtype.ext (congrFun hab i)

theorem original {n:ℕ}(R:Run G)(W:Initialize G)(D d:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
    (N K j c host:ℕ)(hc:host≤c)(cK:c≤K)(KN:K≤N)(simple:G.Simple)(ratio:LocalRatio R.metals.O)
    (S:Finset (Fin (n+1)))[Nonempty S](fill:∀i,(R.family.labels.level (d i)).Index)
    (v:∀i,(R.family.labels.level (d i)).Coeff)(φ:Fin (n+1)→ℂ→L[ℝ]ℝ)(T:(i:Fin (n+1))→Rarity (D i))
    (y:ℝ)(o:CellR)(nodes:Finset (S→ Cover))
    (contains:∀z,weight D d S T (paceT R.family.path.levels.S j K) y o z≠0→z∈nodes):
    (∑z∈nodes,weight D d S T (paceT R.family.path.levels.S j K) y o z •
      node R D d N K c host S fill v φ z)=logged R D d j K N host c S fill v φ T y o:=by
  let L:=R.family.path.levels
  let x:=paceT L.S j K
  let emb:=location D S T x y o
  let visits:=univ.map emb
  let F (z:S→ Cover):=weight D d S T x y o z • node R D d N K c host S fill v φ z
  have returned:logged R D d j K N host c S fill v φ T y o=∑z∈visits,F z:=by
    unfold logged
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro z _
    rw [WilsonPositionProgramTrialPublicSocketFactors.original R W D d cut S fill v φ _ L R.metals.O simple ratio
      N _ host c K hc cK KN]
    change _ • _=weight D d S T x y o (emb z) • node R D d N K c host S fill v φ (emb z)
    congr 1
    rw [←Finset.prod_coe_sort]
    simp [weight,WilsonPositionProgramTrialPublicPulse.frame,sites,emb,location,x,L]
  have hit (z:S→ Cover)(nz:weight D d S T x y o z≠0):z∈visits:=by
    have inside (i:S):z i∈VisitsT (T i) x y o:=by
      apply (visiting (pace_pos L.S j K)).mpr
      intro silent
      change wheelC x y (z i) (T i).ψ o=0 at silent
      apply nz
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [held,silent])
    exact Finset.mem_map.mpr ⟨fun i=>⟨z i,inside i⟩,mem_univ _,rfl⟩
  rw [returned]
  change (∑z∈nodes,F z)=∑z∈visits,F z
  calc
    _=∑z∈nodes∪visits,F z:=Finset.sum_subset (subset_union_left ..) (by
      intro z _ outside
      have hz:weight D d S T x y o z=0:=by by_contra nonzero;exact outside (contains z nonzero)
      simp only [F,hz,zero_smul])
    _=_:=(Finset.sum_subset (subset_union_right ..) (by
      intro z _ outside
      have hz:weight D d S T x y o z=0:=by by_contra nonzero;exact outside (hit z nonzero)
      simp only [F,hz,zero_smul])).symm

end YM.Integration.WilsonPositionProgramTrialPublicCellVisits
end
