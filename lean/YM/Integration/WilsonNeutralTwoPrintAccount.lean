import YM.Integration.WilsonNeutralTwoPrintPeg
import YM.Integration.WilsonCapturedPrimaryWindingColoredCatalogue

/-! Two paid physical words with independent Laurent clearings, on the same
original torus. The scalar and all mixed time/link derivatives use the signed
difference of the two native finite tables. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintAccount
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.RG02.Adjacent Comparison.Density
open FVA1Physical FVA1Physical.TwoReset Exterior Further.PhysicalPeriodLimitF933 Macrame
open AnalyticBridge.SectorAffine.Offset RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Diagram
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open WilsonIndependentCapturedAngularWinding WilsonEmittedAngularJointFare
open WilsonCapturedPinnedColorFile
open WilsonCapturedPrimaryWindingMaterialRead (nativeClock)
open WilsonOriginalMarkedFaceReading
open WilsonNeutralTwoPrintFronts (table)
open private difference from YM.Integration.WilsonEmittedFiledThermalGerm
open WilsonNeutralTwoPrintPeg (phase allowed)
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{C:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}
  (M:(a:Bool)→I a→Row (P a) C G (X a))(x:(a:Bool)→X a)(grades:Bool→V→ℕ)
  {w:Bool→V→ℝ}{σ cost:Bool→ℝ}{order seats shelf:Bool→ℕ}
  (stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (cost a) (order a) (seats a) (shelf a))
  (s:Multi.Hot C)(v:s.val.val)(layout:Bool→Layout G)(tape:Bool→Finset Age)
  (proper:∀a,Legal (tape a) (layout a))
local notation "q" a:max => (fun i:I a=>(M a i).paint (x a))
local notation "bank" a:max p:max => table (M a) (x a) (grades a) (layout a) (tape a) s (phase p)
local notation "pupil" a:max e:max B:max => (peek dvd_rfl (M a) (grades a) (layout a) (tape a) (x a) e B).part s.val
local notation "native" a:max => Launch.index C (grades a) s.val+1
local notation "signal" a:max p:max => channel (phase p) (WilsonOriginalMarkedFaceReading.field
  (Air.craft (M a) (q a) (grades a) (layout a) (tape a)) s (Stock.census Unit))
abbrev sign (a:Bool):ℝ:=if a then -1 else 1

def entry (e r:ℕ)(z:Fin r→SiteSlot G n):ℂ:=
  (((bank false false) e r z-(bank true false) e r z:ℝ):ℂ)+
    (((bank false true) e r z-(bank true true) e r z:ℝ):ℂ)*Complex.I

theorem scalar (e:ℕ)(z:Fin 0→SiteSlot G n):
    entry M x grades s layout tape e 0 z=pupil false e 0-pupil true e 0:=by
  unfold entry
  simp only [WilsonNeutralTwoPrintFronts.scalar]
  change (((pupil false e 0).re-(pupil true e 0).re:ℝ):ℂ)+
    (((pupil false e 0).im-(pupil true e 0).im:ℝ):ℂ)*Complex.I=_
  rw [←Complex.sub_re,←Complex.sub_im,Complex.re_add_im]

variable (ℓ:Bool→ℕ)(B₀:BudgetPoint){K θ:Bool→ℝ}{g:ℝ}
  (scope:∀a,Invoice.Supports B₀ (K a) (B₀.supportExponent+2) g (σ a) (θ a))

local notation "full" => (fun z:Chart G n=> words M x sign ℓ (fun a=>picked (M a) s.val) z.1 (increment 1 z.2))

include stock scope v proper in
theorem read (head J:ℕ)(closed:∀a,ℓ a+(native a)=head)
    {ε:ℝ}(positive:0≤ε)(winding:∀e,e+head<J →
      ((e+head).factorial:ℝ)*mass (entry M x grades s layout tape e) (e+head)≤ε):
    ∀d<J,∑i:Fin d→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ d full 0 (WilsonEmittedRootedJetWage.peg G n ∘ i)‖≤ε:=by
  have sm:=WilsonEmittedFiledGerm.smooth M w grades x sign ℓ B₀ stock scope s layout tape
  intro d hd
  let chosen (a:Bool)(t:ℕ)(A:Link G n):=pupil a t A
  have heard (A:Link G n):Assembly.jet full d (1,edgeColor A)=
      if head≤d then chosen false (d-head) A-chosen true (d-head) A else 0:=by
    rw [WilsonCapturedPrimaryWindingColoredCatalogue.seen M w grades x sign ℓ B₀ stock scope s layout tape]
    simp only [Fintype.sum_bool,sign,if_true,one_smul,neg_smul]
    unfold WilsonCapturedPrimaryWindingStockRead.printed
    simp only [closed,Nat.sub_sub]
    split <;> simp [chosen,sub_eq_add_neg,add_comm]
  by_cases active:head≤d
  · let e:=d-head
    have index:e+head=d:=by dsimp [e];omega
    have value (a p:Bool)(A:Link G n):
        (phase p (chosen a e A):ℂ)=WilsonIndependentCapturedFiledDirections.value ((bank a p) e) d A:=by
      have data:=WilsonNeutralTwoPrintFronts.issued (M a) (x a) (grades a) (layout a) (tape a) s (phase p)
        (stock a) (WilsonEmittedFiledCatalogue.width B₀ scope a) (proper a) v (allowed p) e e 1 Nat.zero_lt_one
      have issue:=data.2.1
      have nativeRead:WilsonEmittedFiledDeckFare.row nativeClock (signal a p) () e A=
          WilsonIndependentCapturedFiledDirections.value ((bank a p) e) (e+(native a)) A:=by
        have raw:See.noseC (Stock.census Unit) () nativeClock (signal a p) e (Stationary.arm G n 1 A)=
            Booth.Uniforms.cuff (bank a p) (native a) e (Stationary.arm G n 1 A):=
          issue.earned e le_rfl _
        unfold WilsonEmittedFiledDeckFare.row
        rw [raw,Booth.Uniforms.cuff,Binding.flavor_lo]
        rfl
      rw [data.2.2.2 e A] at nativeRead
      rw [WilsonIndependentCapturedFiledDirections.value,
        ←pack_extends (issue.grade e) (show e+(native a)≤d by have h:=closed a;omega)]
      exact nativeRead
    apply (WilsonCapturedPrimaryWindingColoredPeg.census full d (sm.of_le le_top)
      (entry M x grades s layout tape e) ?_).trans
    · simpa only [index] using winding e (by omega)
    intro A
    rw [heard,if_pos active]
    change chosen false e A-chosen true e A=_
    let delta:=chosen false e A-chosen true e A
    have reconstruct:delta=((phase false (chosen false e A):ℂ)-(phase false (chosen true e A):ℂ))+
        ((phase true (chosen false e A):ℂ)-(phase true (chosen true e A):ℂ))*Complex.I:=by
      rw [←Complex.ofReal_sub,←Complex.ofReal_sub,←map_sub,←map_sub]
      exact (Complex.re_add_im _).symm
    apply reconstruct.trans
    rw [value false false,value true false,value false true,value true true]
    rw [difference,difference]
    simp only [entry,held,sum_mul,←sum_add_distrib]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro z _
    ring
  · apply (WilsonCapturedPrimaryWindingColoredPeg.census full d (sm.of_le le_top) (fun _ _=>0) ?_).trans
    · simpa [mass] using positive
    intro A
    rw [heard,if_neg active]
    simp [held]

end YM.Integration.WilsonNeutralTwoPrintAccount
end
