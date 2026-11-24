import YM.Integration.WilsonPositionProgramTrialPublicPulse
import YM.Integration.WilsonPositionProgramTrialHomeFaces

/-! Restore the actual registered home material on the same old-N trajectory. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCensus
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
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem reindex {a:ℕ}{S:Finset I}[Nonempty S](idx:Fin (a+1)≃S)
    (P:(i:S)→Era G ℝ)(d:S→ℕ)(paid:∀i,Auth (d i) (P i)):
    gather P ordered=MassP G ℝ a (P∘idx):=by
  have left:=WilsonPositionProgramTrialPublicGather.funded P d paid (ordered (I:=S))
  have right:=manCo (P∘idx) (d∘idx) (fun j=>paid (idx j))
  apply WilsonIndependentMatchedOpeningFaithful.original
    (left.tall (le_max_left _ (∑j,d (idx j)))) (right.tall (le_max_right _ _))
  intro t v
  rw [WilsonPositionProgramTrialPublicGather.read P d paid t v ordered,entered.product,
    WilsonIndependentMatchedOpeningMass.cash (P∘idx) (d∘idx) (fun j=>paid (idx j)) t v]
  simpa only [Function.comp_apply] using
    (Equiv.prod_comp idx (fun i:S=>WilsonIndependentMatchedOrdinarySeat.here t v (flash ((P i).1 t)))).symm

local notation "C" => Credit.leanC
variable {n e k u:ℕ}
local notation "Lib" => Fin (n+1)

theorem original (R:Run G)(W:Initialize G)(D d:Lib→ℕ)(cut:∀i,d i<D i)
    (own:∀i,Rails (d i) k u e)(α:∀i,Alma (R.family.labels.level (d i))→ℝ)(Z B:Lib→Credit)
    (N j c K host:ℕ)(hc:host≤c)(cK:c≤K)(KN:K≤N)(simple:G.Simple)(ratio:LocalRatio R.metals.O)
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:Lib→ℂ→L[ℝ]ℝ)(S:Finset Lib)[Nonempty S]{a:ℕ}(idx:Fin (a+1)≃S)
    (X:∀i,CutsP (hol G) ((deck (G:=G) d D cut) i).ans ((deck (G:=G) d D cut) i).path (own i) C C C C)
    (file:Filed R W d D cut (fun _=>false) own (fun i=>written _ (v i) (φ i)) α Z B j K N X)
    (T:(i:Lib)→Rarity (D i))(x:Lib→ℝ)(xp:∀i,0<x i)(y:ℝ)(o:Lib→CellR):
    let L:=R.family.path.levels
    let O:=R.metals.O
    (∑z:choices D T x y o S,portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ
      (frame D d T x y o S z) L O N (digits L K (sites D T x y o S z)) host c K
      (here L K (sites D T x y o S z) c))=
    cruises L O N (mass d S) K host (MassP G ℝ a (fun p=>let i:Lib:=idx p
      word (X i).pt (T i) (x i) y (o i) (d i))):=by
  dsimp only
  rw [WilsonPositionProgramTrialPublicPulse.original R W D d cut S fill v φ T x xp y o _ _ simple ratio N
    host c K hc cK KN]
  let P (i:Lib):=word (Shrine (plate (sectionAt R W false (d i)) (cut i)) (written _ (v i) (φ i)))
    (T i) (x i) y (o i) (d i)
  have pay (i:Lib):Auth (d i) (P i):=by
    unfold P
    rw [WilsonPositionProgramTrialPublicSpatialSum.leg R W (cut i) _ _ _ _ _ _ (xp i)]
    exact Auth.sum fun _ _=>WilsonIndependentMatchedOpeningFiled.enrolled ..
  have exactBirth (i:Lib):(X i).pt=Shrine (plate (sectionAt R W false (d i)) (cut i)) (written _ (v i) (φ i)):=by
    obtain ⟨_,_,_,_,_,_,exactBirth,_⟩:=(file i).1
    exact exactBirth
  apply congrArg (cruises _ _ N (mass d S) K host)
  simp_rw [exactBirth]
  exact reindex idx (fun i:S=>P i) (fun i:S=>d i) (fun i:S=>pay i)

end YM.Integration.WilsonPositionProgramTrialPublicCensus
end
