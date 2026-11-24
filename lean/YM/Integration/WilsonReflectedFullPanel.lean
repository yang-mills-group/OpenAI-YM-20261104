import YM.Integration.WilsonReflectedFourStations
import YM.Integration.WilsonAddressedRestartedFiled
import YM.Integration.WilsonOriginalMicroscopicGuardedPage

/-! A finite panel of actual public fields. One source's inverse and its
whole pre-cutoff fitting are used for every opposite field in the panel.
Its signed comparison at a finer date keeps its full measured section
projection and its original forced allowance. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedFullPanel
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open GapsContact GapsContact.Seams GapsContact.Stamps Analysis Table Extraction Bid Spec Ascent Trace
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Next.Rank.Price
open PhysicalNext PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals
open WilsonReflectedOriginalTwoDeposit WilsonReflectedOriginalVanes WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedReporters WilsonOriginalMicroscopicGuardedWallet
open scoped Classical BigOperators Topology
open WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonAddressedRestartedColumn WilsonPositionProgramBlockedPublicExperiment
open WilsonOriginalMicroscopicGuardedPage
variable {G:Gauge}(R:Run G){h:Extraction.Order}{S:Table R.family.book}(F:Final R.family h S)
    (l:Ultrafilter (ℕ×ℕ))
local notation "C₀" => R.family
local notation "A₀" => R.family.path.levels
local notation "F₀" d:max => R.family.labels.level d

def receipt (d j K N p q:ℕ)(before:j ≤ K)(high:K ≤ N)(η:ℝ)
    (M:(C₀).label d ≃ₗ[ℂ] (C₀).label d)(Y:(C₀).label d)(cash:ℝ):Prop:=
  let y:=((C₀).factory d N p).terminal.symm Y
  let e:=full R d N p j Y
  let w:=M.symm e
  let T:=numerator R d N p K 0 w
  let rateK:=(1+4*stock C₀ K)*(F₀ d).coeffSize w
  Arrived R d j K N p q before high η M e ∧
    (F₀ d).coeffSize w ≤ WilsonOriginalMicroscopicGuardedReporters.stretch R η j K*
      ((1+wrapCost R d j)*cash) ∧
    ∀f,j ≤ f → f ≤ K → ∀o:Site ((C₀).side f p),∃z:store C₀ d p f,
      WilsonAddressedRestartedFiled.Filed R d N p f o
        (track R d N p K T f-calValues (C:=C₀) d N p f y) (hike C₀ K f rate*rateK) z

theorem original {I:Type}[Fintype I](simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((A₀).budget j).supportExponent)(law:OPE.Therm.Poetry (A₀))
    (d:I→ℕ)(q:ℕ){η:ℝ}(pos:0<η):
    ∃floor:ℕ,∀(r B:I→ℝ)(j m:I→ℕ)(v:∀a:I,S.Field (d a)),
    (∀a,floor ≤ j a) → (∀a,BookedArm F l (r a) (j a) (m a) (d a) (B a)) →
    ∃Y:∀a:I,ℕ×ℕ→(C₀).label (d a),
      (∀a,Captured R F l (r a) (B a) (j a) (m a) (d a) (v a) (Y a)) ∧
      ∀K (before:∀a,j a ≤ K) N p (high:K ≤ N), (∀a,j a<N) →
        ∃M:∀a:I,(C₀).label (d a) ≃ₗ[ℂ] (C₀).label (d a),
          ∀a,receipt R (d a) (j a) K N p q (before a) high η (M a) (Y a (N,p))
            ((C₀).S.a (j a)^(d a)*B a*cost F (d a) (r a) (v a)):=by
  classical
  choose first offer using fun a:I=>WilsonOriginalMicroscopicGuardedReporters.original R (fun _=>d a) simple shop wide law q pos
  choose second file using fun a:I=>eventually_atTop.mp (WilsonAddressedRestartedFiled.original R (d a) simple)
  let floor (a:I):ℕ:=max (first a) (max (second a) (R.t (d a)))
  refine ⟨univ.sup floor,?_⟩
  intro r B j m v early booked
  choose Y src using fun a:I=>enrolled R F l (v a) (booked a)
  refine ⟨Y,src,?_⟩
  intro K before N p high live
  have start (a:I):floor a ≤ j a:=(le_sup (mem_univ a)).trans (early a)
  have one (a:I):∃M,∀e,Arrived R (d a) (j a) K N p q (before a) high η M e:=by
    obtain ⟨M,bought,_⟩:=offer a (fun _=>j a) (fun _=>(le_max_left ..).trans (start a)) K
      (fun _=>before a) (fun _=>0) N p high (fun _=>live a)
    exact ⟨M 0,bought 0⟩
  choose M funded using one
  refine ⟨M,?_⟩
  intro a
  let Y₀:=Y a (N,p)
  let y:=((C₀).factory (d a) N p).terminal.symm Y₀
  let e:=full R (d a) N p (j a) Y₀
  have fit:=funded a e
  have row:=WilsonOriginalMicroscopicGuardedPage.wage (p:=p) R (d a)
    (show R.t (d a) ≤ j a from (le_max_right ..).trans ((le_max_right ..).trans (start a)))
    (src a).reference (live a).le (wide _) Y₀
  have magnitude:0 ≤ 1+wrapCost R (d a) (j a):=by
    have w:0 ≤ WilsonCapturedPrimaryCoreBill.wrapFee (F₀ (d a)) (C₀).params:=mul_nonneg (Nat.cast_nonneg _) (germ_close (F₀ (d a)) (C₀).params).choose_spec.1.le
    exact add_nonneg zero_le_one (mul_nonneg (mul_nonneg w (Real.exp_nonneg _)) (zero_le_one.trans ((A₀).params _).columns_ge))
  refine ⟨fit,(fit.1).trans (mul_le_mul_of_nonneg_left (row.2.trans (mul_le_mul_of_nonneg_left
    ((src a).quota N p (live a)) magnitude)) (by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity)),?_⟩
  intro f jf fK o
  have same:e=page (C:=C₀) (d a) p (j a) (((C₀).factory (d a) N p).entries (j a) y):=
    page_at R (d a) (live a).le Y₀
  rw [same] at fit
  have made:=file a (j a) ((le_max_left ..).trans ((le_max_right ..).trans (start a))) N p K (before a) high q η (M a) y fit f jf fK o
  rw [←same] at made
  exact made

end YM.Integration.WilsonReflectedFullPanel
end
