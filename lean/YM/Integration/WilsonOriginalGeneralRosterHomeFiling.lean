import YM.Integration.WilsonOriginalGeneralRosterHomeRooms
import YM.Integration.WilsonOriginalGeneralRosterHomeArms

/-! The entire named physical collection has one genuine cutoff deposit, chosen
before any test pose, subroster or second copy. Each posed panel on the common
stock reads that very deposit, with its own engineering factor and phase. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeFiling
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialStationHome (chargeAt mass Seated)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n h D k u e:ℕ}{T:Type*}[Fintype T]
local notation "C" => Credit.leanC

open WilsonPositionProgramTrialHomeFaces (Filed)

open Extra.Histories Motion
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonOriginalGeneralRosterHomeArms (component)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonOriginalPublicNodalDeployedVote (deployed)
open WilsonOriginalObservedRoseCorrectedWords (votes)

def corrected (R:Run G)(d:(Fin (n+1))→ℕ)(j:(Fin (n+1))→ℕ)(K N per:ℕ)
    (A:∀i,R.family.label (d i)≃ₗ[ℂ]R.family.label (d i))
    (Y:∀i,R.family.label (d i))(direction:(Fin (n+1))→Motion)(i:(Fin (n+1))):R.family.label (d i):=
  (((R.family.S.a K:ℂ)^(d i))⁻¹) • Motion.patch (R.family.labels.level (d i)) (direction i)
    ((A i).symm (fitted R (d i) (j i) N per (Y i)))

def recorded (R:Run G)(d:(Fin (n+1))→ℕ)(j:(Fin (n+1))→ℕ)(K N per:ℕ)(A:∀i,R.family.label (d i)≃ₗ[ℂ]R.family.label (d i))
    (v:∀i,R.family.label (d i))(motion:(Fin (n+1))→Motion)(size:(Fin (n+1))→ℝ)(label:(Fin (n+1))→ℂ)(p:(Fin (n+1))→ℂ→L[ℝ]ℝ)
    (i:(Fin (n+1))):Verse (R.family.labels.level (d i)):=written (R.family.labels.level (d i))
      (deployed R (d i) K (N,per) (corrected R d j K N per A v motion i))
      (component R (d i) K (size i) (label i) (p i))

variable (R:Run G)(W:Initialize G)(d cap:(Fin (n+1))→ℕ)(fit:∀i,d i<cap i)(kind:(Fin (n+1))→Bool)(own:∀i,Rails (d i) k u e)
  (α:∀i,Alma (R.family.labels.level (d i))→ℝ)(Z B:(Fin (n+1))→Credit)(m K N per:ℕ)
  (station:(Fin (n+1))→ℕ)(axes:∀i,R.family.label (d i)≃ₗ[ℂ]R.family.label (d i))
  (Y:∀i,R.family.label (d i))(direction:(Fin (n+1))→Motion)(radius:(Fin (n+1))→ℝ)(t:(Fin (n+1))→ℂ)(phase:(Fin (n+1))→ℂ→L[ℝ]ℝ)

def Enrolled (R:Run G)(W:Initialize G)(d cap:(Fin (n+1))→ℕ)(fit:∀i,d i<cap i)(kind:(Fin (n+1))→Bool)(own:∀i,Rails (d i) k u e)
  (α:∀i,Alma (R.family.labels.level (d i))→ℝ)(Z B:(Fin (n+1))→Credit)(m K N per:ℕ)
  (station:(Fin (n+1))→ℕ)(axes:∀i,R.family.label (d i)≃ₗ[ℂ]R.family.label (d i))
  (Y:∀i,R.family.label (d i))(direction:(Fin (n+1))→Motion)(radius:(Fin (n+1))→ℝ)(t:(Fin (n+1))→ℂ)(phase:(Fin (n+1))→ℂ→L[ℝ]ℝ):Prop:=
  let Q:=deck (G:=G) d cap fit
  let field:=recorded R d station K N per axes Y direction radius t phase
  ∃X:∀i,CutsP (hol G) (Q i).ans (Q i).path (own i) C C C C,
    Filed R W d cap fit kind own field α Z B m K N X ∧
    ∀(b:ℕ)(leg:Fin (b+1)→(Fin (n+1)))(f req power tag:ℕ)(credit:ℝ)(fk:f≤K)(kn:K≤N),
    ∀(file:WilsonMovingForkHeterogeneousCut.Filed R (d ∘ leg) K)
      (panel:Panel R (d ∘ leg) N per f K fk kn req power tag credit),
    file.station=station ∘ leg→file.A N per=(fun i=>axes (leg i))→
    panel.slot=file.station→panel.axis=file.A N per→panel.names=(fun i=>Y (leg i))→panel.turn=direction ∘ leg→
    ∃arms:∀i,Arm R (d (leg i)) N per f K,
      (∀i,(arms i).Y=Y (leg i) ∧ (arms i).w=(axes (leg i)).symm
        (fitted R (d (leg i)) (station (leg i)) N per (Y (leg i))) ∧
        (arms i).b=(direction (leg i)).2 ∧ (arms i).s=(direction (leg i)).1 ∧ (arms i).o=panel.loc i) ∧
      Filed R W (d ∘ leg) (cap ∘ leg) (fun i=>fit (leg i)) (kind ∘ leg) (fun i=>own (leg i))
        (fun i=>written (R.family.labels.level (d (leg i)))
          (amounts R (d (leg i)) K N per (radius (leg i)) (t (leg i)) (coords R (arms i))) (phase (leg i)))
        (fun i=>α (leg i)) (Z ∘ leg) (B ∘ leg) m K N (fun i=>X (leg i))

theorem place {X:∀i,CutsP (hol G) ((deck (G:=G) d cap fit) i).ans ((deck (G:=G) d cap fit) i).path (own i) C C C C}
    (admitted:Filed R W d cap fit kind own (recorded R d station K N per axes Y direction radius t phase) α Z B m K N X):
    Enrolled R W d cap fit kind own α Z B m K N per station axes Y direction radius t phase:=by
  refine ⟨X,admitted,?_⟩
  intro b leg f req power tag credit fk kn file panel dates pin stations matrices names turns
  obtain ⟨arms,paid,_read,heard⟩:=WilsonOriginalGeneralRosterHomeArms.original R (d ∘ leg) panel file stations matrices
  have idVote(i):votes R (d ∘ leg) (N:=N) (per:=per) file panel.names panel.turn i=corrected R d station K N per axes Y direction (leg i):=by
    simp only [WilsonOriginalObservedRoseCorrectedWords.votes,WilsonMovingForkMixedSeed.units,WilsonMovingForkMixedSeed.doses,corrected,dates,pin,names,turns,Function.comp_apply]
    rfl
  refine ⟨arms,?_,?_⟩
  · intro i
    have receipt:=paid i
    simp only [dates,pin,names,turns,Function.comp_apply] at receipt
    exact receipt
  · have identity:(fun i=>written (R.family.labels.level (d (leg i)))
        (amounts R (d (leg i)) K N per (radius (leg i)) (t (leg i)) (coords R (arms i))) (phase (leg i)))=
        fun i=> (recorded R d station K N per axes Y direction radius t phase) (leg i):=by
      funext i
      exact (heard i (radius (leg i)) (t (leg i)) (phase (leg i))).trans (by rw [idVote];rfl)
    rw [identity]
    exact WilsonOriginalGeneralRosterHomeRooms.select admitted leg

theorem original (simple:G.Simple)(ξ:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices ξ R.kit):
    ∃α:∀i,Alma (R.family.labels.level (d i))→ℝ,(∀i a,0≤α i a) ∧
    ∃Z B:(Fin (n+1))→Credit,∀ᶠfloor:ℕ in atTop,∀m K N per,floor ≤ m → m ≤ K → K ≤ N → 
    ∀(j:(Fin (n+1))→ℕ)(A:∀i,R.family.label (d i)≃ₗ[ℂ]R.family.label (d i))(v:∀i,R.family.label (d i))
      (motion:(Fin (n+1))→Motion)(size:(Fin (n+1))→ℝ)(label:(Fin (n+1))→ℂ)(p:(Fin (n+1))→ℂ→L[ℝ]ℝ),
      Enrolled R W d cap fit kind own α Z B m K N per j A v motion size label p:=by
  obtain ⟨α,nn,Z,B,grant⟩:=WilsonOriginalGeneralRosterHomeRooms.original R W simple ξ funded d cap fit kind own
  refine ⟨α,nn,Z,B,?_⟩
  filter_upwards [grant] with floor charged
  intro m K N per mature before live j A v motion size label p
  let c:=fun i:(Fin (n+1))=>written (R.family.labels.level (d i))
    (deployed R (d i) K (N,per) (corrected R d j K N per A v motion i))
    (component R (d i) K (size i) (label i) (p i))
  obtain ⟨X,installed⟩:=charged m K N mature before live c
  exact place R W d cap fit kind own α Z B m K N per j A v motion size label p installed

end YM.Integration.WilsonOriginalGeneralRosterHomeFiling
end
