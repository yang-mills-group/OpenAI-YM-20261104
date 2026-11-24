import YM.Integration.WilsonNeutralTwoPrintFronts
import YM.Integration.WilsonNeutralTwoPrintReset
import YM.Integration.WilsonCapturedPrimaryWindingColoredPeg

/-! The complete rooted mixed-peg invoice of two independently deposited
compact catalogues, including the unsummed signed occupied constant. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPeg
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary AllOrder AllOrder.Floe
open Exterior Comparison.RG02 Comparison.RG02.Adjacent Multi FVA1Physical FVA1Physical.TwoReset
open Further.PhysicalPeriodLimitF933 Macrame
open WilsonOriginalMarkedFaceReading WilsonCapturedPinnedColorFile
open WilsonCapturedPrimaryWindingMaterialRead (nativeClock)
open WilsonNeutralTwoPrintFronts (table)
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedAngularJointFare
open WilsonIndependentCapturedAngularWinding WilsonIndependentCapturedFiledDirections
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{C:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}
  (M:(a:Bool)→I a→Row (P a) C G (X a))(x:(a:Bool)→X a)(grades:V→ℕ)
  {w:Bool→V→ℝ}{σ cost:Bool→ℝ}{order seats shelf:Bool→ℕ}
  (stock:∀a,Scene.Armada (M a) (w a) grades (σ a) (cost a) (order a) (seats a) (shelf a))
  (positive:∀a,0<σ a)(s:Hot C)(v:s.val.val)
  (layout:Bool→Layout G)(tape:Bool→Finset Age)(proper:∀a,Legal (tape a) (layout a))

def phase (p:Bool):ℂ→L[ℝ]ℝ:=if p then Complex.imCLM else Complex.reCLM

theorem allowed (p:Bool):LipschitzWith 1 (phase p):=by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [NNReal.coe_one,one_mul,dist_eq_norm,dist_eq_norm,←map_sub]
  cases p
  · change ‖(u-v).re‖ ≤ _
    rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  · change ‖(u-v).im‖ ≤ _
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
local notation "one" a:max => WilsonOriginalMarkedFaceReading.field
  (Air.craft (M a) (fun i=>(M a i).paint (x a)) grades (layout a) (tape a)) s (Stock.census Unit)
local notation "field₀" a:max => WilsonEmittedRootCensus.field (M a) (fun i=>(M a i).paint (x a)) (picked (M a) s.val)
local notation "pole" => Launch.index C grades s.val+1
local notation "bank" a:max p:max => table (M a) (x a) grades (layout a) (tape a) s (phase p)
local notation "pupil" a:max d:max z:max => (peek dvd_rfl (M a) grades (layout a) (tape a) (x a) d z).part s.val

include stock positive proper v in
theorem original (e:ℕ):
    let d:=e+(pole)
    let F:=fun z:Chart G n=>(field₀ false) z - (field₀ true) z
    let b:=fun (p:Bool)(r:ℕ)(z:Fin r→SiteSlot G n)=>(((bank false p) e r z-(bank true p) e r z:ℝ):ℂ)
    (∀(p:Bool)(z:Fin 0→SiteSlot G n),b p 0 z=(phase p ((pupil false e 0) - (pupil true e 0)):ℂ)) ∧
    (∑i:Fin d→WilsonEmittedRootedJetWage.Slot G n,‖iteratedFDeriv ℝ d F 0 (WilsonEmittedRootedJetWage.peg G n ∘ i)‖)
       ≤ (d.factorial:ℝ)*(mass (b false) d+mass (b true) d):=by
  intro d F b
  constructor
  · intro p z
    dsimp only [b]
    rw [WilsonNeutralTwoPrintFronts.scalar,WilsonNeutralTwoPrintFronts.scalar,map_sub]
  · have staff (a:Bool):=Air.license (M a) (fun i=>(M a i).paint (x a)) grades (w a)
        (stock a) (positive a) (fun i=>(stock a).honor i (x a))
    have sm (a:Bool):=WilsonEmittedRecordedJet.analytic (M a) (x a) grades (staff a) (layout a) (tape a) s
    let A (a p:Bool):=bank a p
    let Z (a p:Bool):=channel (phase p) (one a)
    have data (a p:Bool):=WilsonNeutralTwoPrintFronts.issued (M a) (x a) grades (layout a) (tape a) s
      (phase p) (stock a) (positive a) (proper a) v (allowed p) e e 1 Nat.zero_lt_one
    apply WilsonCapturedPrimaryWindingColoredPeg.two F () nativeClock nativeClock (Z false) (Z true)
      (A false) (A true) le_rfl (fun p=>(data false p).2.1) (fun p=>(data true p).2.1)
      (((sm false).sub (sm true)).of_le le_top)
    intro B
    have certificate (a:Bool):
        Assembly.jet (field₀ a) d (1,edgeColor B)=pupil a e B:=by
      have hit:=WilsonNeutralTwoPrintReset.row (M a) (x a) grades (staff a) s (layout a) (tape a) 0 d (edgeColor B)
      have enough:pole≤d:=by dsimp [d];omega
      have index:d-pole=e:=by dsimp [d];omega
      have posB:WilsonCubicOriginalTorus.coordinates G n (edgeColor B)=B:=by
        change edgeColor.symm (edgeColor B)=B
        exact ContinuousLinearEquiv.symm_apply_apply _ _
      simpa only [pow_zero,one_smul,zero_add,Nat.sub_zero,if_pos enough,index,
        posB] using hit
    have sub:Assembly.jet F d (1,edgeColor B)=Assembly.jet (field₀ false) d (1,edgeColor B)-
        Assembly.jet (field₀ true) d (1,edgeColor B):=by
      unfold Assembly.jet
      change _ • iteratedFDeriv ℝ d ((field₀ false)-(field₀ true)) 0 _=_
      rw [iteratedFDeriv_sub_apply ((sm false).of_le le_top) ((sm true).of_le le_top)]
      exact smul_sub ..
    rw [sub,certificate false,certificate true]
    have value (a p:Bool):WilsonEmittedFiledDeckFare.row nativeClock (Z a p) () e B=
        (phase p (pupil a e B):ℂ):=(data a p).2.2.2 e B
    rw [value false false,value true false,value false true,value true true]
    change _=(((pupil false e B).re:ℂ)-(pupil true e B).re)+
      (((pupil false e B).im:ℂ)-(pupil true e B).im)*Complex.I
    rw [←Complex.ofReal_sub,←Complex.ofReal_sub,←Complex.sub_re,←Complex.sub_im,Complex.re_add_im]

end YM.Integration.WilsonNeutralTwoPrintPeg
end
