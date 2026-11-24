import YM.Integration.WilsonPositionProgramTrialChargedFaces
import YM.Integration.WilsonPositionProgramTrialProbeFit

/-! The numerical public coordinate is fixed by the actual compensated K letter on
the original N history. It is the same on every appointment of that letter. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicHome
open Function Filter Finset Matrix Lattice Wilson RG Precision Source Labels
open PhysicalNext.Repeat.Legato XSpace XSpace.Rose RG.Supply Next.Foundations Extra.Histories
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonPositionProgramTrialAccrued (home)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialStationHome (Seated)
open WilsonPositionProgramTrialProbeFit (compact fit income)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){h D k u e:ℕ}
local notation "CC" => Credit.leanC

def label (N per K:ℕ)(r:ℝ)(t:ℂ)(plane:ℂ→L[ℝ]ℝ)(v:R.family.label h):
    Verse (R.family.labels.level h):=
  written (R.family.labels.level h) (amounts R h K N per r t v) plane

def declared (Q:SealR G)(k m K N:ℕ)(c:Q.Rider):Q.Rider:=
  income Q R.family.path.levels R.metals.O N k m (K-m) c

theorem original (Q:SealR G){rail:Rails Q.h k u e}{m K N:ℕ}(c:Q.Rider){fuel:ℝ}
    (X:CutsP (hol G) Q.ans Q.path rail CC CC CC CC)
    (seated:Seated R Q rail m K N (compact Q c) fuel X):
    home Q X=declared R Q k m K N c ∧
    received R.family.path.levels R.metals.O Q m K N (declared R Q k m K N c)=X.tileP ∧
    compact Q c=centralL R.family.path.levels R.metals.O N m K Q
      (PermuteLens R.family.path.levels R.metals.O Q N m (declared R Q k m K N c))+X.springP X.i:=by
  obtain ⟨lv,chart,start,stop,top,_,entered,_⟩:=seated
  have date:X.i=K-m:=by have hK:X.m+X.i=K:=stop; omega
  have fixed:home Q X=declared R Q k m K N c:=by
    unfold home declared WilsonPositionProgramTrialProbeFit.income
    rw [lv,chart,top,start,date,entered]
  refine ⟨fixed,?_,?_⟩
  · simpa only [lv,chart,start,stop,top,fixed] using (WilsonPositionProgramTrialAccrued.returns Q X).1
  · simpa only [lv,chart,start,stop,top,entered,fixed] using WilsonPositionProgramTrialAccrued.source Q X

theorem placed {N per f K:ℕ}(A:Arm R h N per f K)(r:ℝ)(t:ℂ)(plane:ℂ→L[ℝ]ℝ)
    (v:R.family.label h)(spin:Signed)(hand:Bool)(hv:A.w=v)(hs:A.s=spin)(hb:A.b=hand):
    label R N per K r t plane (coords R A)=
      label R N per K r t plane (Motion.patch (R.family.labels.level h) (spin,hand) v):=by
  rw [coords,hv,hs,hb]

end YM.Integration.WilsonPositionProgramTrialPublicHome
end
