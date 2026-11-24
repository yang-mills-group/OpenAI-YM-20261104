import YM.Integration.WilsonMeasuredPublicEntranceMasterUpper
import YM.Integration.WilsonSeparatedPrefixActualDose
import YM.Integration.WilsonSeparatedPrefixHeldValue

/-! All ordinary faces of the appointed public panel at one of the original funded older flats. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixPanelReturn
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial WilsonPositionProgramReportedField
open WilsonMeasuredPublicEntrancePanel (Panel Reading charged)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open PertExtension PertExtension.LatticePT
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per f K u:ℕ}
local notation "C" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin n)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
variable (A:Panel R d N per f K fk cut requested power t B)

def trueFace (s:(J).Mode):Config G ((C).side N per)→ℂ:=fun W=>∏v∈s.val,
  (C).O N per (displayed R (d v) (A.names v) (A.turn v)) (anchorAt R (A.loc v) N) W

def independentFace (file:Filed R d K)(s:(J).Mode):Config G ((C).side K per)→ℂ:=fun W=>
  let w:=fun a=>Motion.patch ((C).labels.level (d a)) (A.turn a)
    (doses R d file.station (N:=N) (per:=per) (file.A N per) A.names a)
  ∏v∈s.val,uncut R (d v) N per K (((C).S.toDepth fk per).embed (A.loc v)) (units R d K w v) W

private theorem cutoff (s:(J).Mode):
    WilsonMeasuredPublicEntrancePanel.Raw R d A s=fun W=>(∏a∈s.val,(charged R d A a:ℂ))*trueFace R d A s W:=by
  funext U
  simp only [WilsonMeasuredPublicEntrancePanel.Raw,trueFace,prod_mul_distrib]

private theorem planted (file:Filed R d K)(station:A.slot=file.station)(axes:A.axis=file.A N per)(s:(J).Mode):
    WilsonMeasuredPublicEntrancePanel.Guard R d A s=fun W=>(∏a∈s.val,(charged R d A a:ℂ))*independentFace R d A file s W:=by
  funext U
  let ξ:=fun a=>((C).S.toDepth fk per).embed (A.loc a)
  let w:=fun a=>Motion.patch ((C).labels.level (d a)) (A.turn a)
    (doses R d file.station (N:=N) (per:=per) (file.A N per) A.names a)
  unfold WilsonMeasuredPublicEntrancePanel.Guard
  rw [axes,station]
  change (∏v∈s.val,∑l,entire R (d v) K (N,per) _ l*WilsonPositionProgramBlockedTrialFiling.atomAt R (d v) N per K (ξ v) l U)=_
  unfold independentFace
  rw [←prod_mul_distrib]
  apply prod_congr rfl;intro v _
  rw [WilsonPositionProgramBlockedTrialFiling.filed R (d v) N per K cut (ξ v),mul_sum]
  apply sum_congr rfl;intro l _
  simp only [entire,gMap,Frame.scaled_apply,units,submitted,WilsonOriginalAlternativeFiniteSource.fired,
    one_mul,Pi.smul_apply,smul_eq_mul,doses]
  ring

theorem measured (file:Filed R d K)(station:A.slot=file.station)(axes:A.axis=file.A N per)(held:u≤f)
    (sale:Reading R d A held)(one:∀a,1≤A.M a)(E:Fin n→ℕ)(refs:∀a b,b≤d a→(C).ref b≤N)
    (fare:∀a,Next.Rank.Spindle.paid (C) (d a) f N per (A.names a)≤A.M a*(H f)^(E a))
    (s:(J).Mode)(desired:ℕ)(exposure:desired+∑a∈s.val,E a≤requested):
    ‖reading R (N:=N) (credit (C) N per 0 (trueFace R d A s) K cut) u (held.trans fk)-
      reading R (N:=N) (numerator R N per K (independentFace R d A file s)) u (held.trans fk)‖
      ≤(∏a∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (d a) (A.M a))*((H f)^desired)⁻¹:=by
  let err:=reading R (N:=N) (credit (C) N per 0 (trueFace R d A s) K cut) u (held.trans fk)-
      reading R (N:=N) (numerator R N per K (independentFace R d A file s)) u (held.trans fk)
  have nc:Continuous (trueFace R d A s):=continuous_finsetProd _ fun _ _=>(C).continuousO _ _ _ _ _
  have kc:Continuous (independentFace R d A file s):=continuous_finsetProd _ fun a _=>
      continuous_const.add (((C).localSection (d a)).continuous_places _ _)
  have nz:(∏a∈s.val,(charged R d A a:ℂ))≠0:=prod_ne_zero_iff.mpr fun a _=>Complex.ofReal_ne_zero.mpr
    (WilsonReflectedPublicCommonDose.positive ..).ne'
  obtain ⟨balance,price⟩:=sale s
  have earned:=WilsonSeparatedPrefixPhysicalCredit.restored R cut (held.trans fk) nc kc _ nz
    (cutoff R d A s) (planted R d A file station axes s) (balance ▸ price)
  have paid:‖err‖≤(∏v∈s.val,‖(charged R d A v:ℂ)‖)⁻¹*((H f)^requested)⁻¹:=by simpa only [norm_prod] using earned
  have smaller:((H f)^requested)⁻¹≤((H f)^(desired+∑a∈s.val,E a))⁻¹:=
    inv_anti₀ (pow_pos (zero_lt_one.trans_le ((C).path.levels.fits.delayed f).le) _)
      (pow_le_pow_right₀ ((C).path.levels.fits.delayed f).le exposure)
  exact WilsonSeparatedPrefixActualDose.original R d A.M E one (fk.trans cut) A.names A.home A.sensors A.stamps
    A.enrolled refs fare s.val desired err (paid.trans (mul_le_mul_of_nonneg_left smaller
      (inv_nonneg.mpr (prod_nonneg fun _ _=>norm_nonneg _))))

theorem original {m apron reserve first j:ℕ}(read:ReadAt R d m N per apron requested t reserve power B first)
    (deep:first≤j)(openJ:m≤j)(height:j+2≤f)(berth:K=WilsonInvariantActionPosition.berth R reserve f)
    (allSlots:∀v,first≤A.slot v)(roots:((Fin n)→False) ∨ Ground R N per j f apron A.loc)
    (top:m≤u)(uj:u≤j)(firstOpen:Trace.Physical.GermGraph.Opened (C) 0 u per)(lastOpen:Trace.Physical.GermGraph.Opened (C) 0 j per)
    (file:Filed R d K)(station:A.slot=file.station)(axes:A.axis=file.A N per)
    (one:∀a,1≤A.M a)(E:Fin n→ℕ)(refs:∀a b,b≤d a→(C).ref b≤N)
    (fare:∀a,Next.Rank.Spindle.paid (C) (d a) f N per (A.names a)≤A.M a*(H f)^(E a))
    (s:(J).Mode)(desired:ℕ)(exposure:desired+∑a∈s.val,E a≤requested):
    let held:=uj.trans ((Nat.le_add_right j 2).trans height)
    ‖reading R (N:=N) (credit (C) N per 0 (trueFace R d A s) K cut) u (held.trans fk)-
      reading R (N:=N) (numerator R N per K (independentFace R d A file s)) u (held.trans fk)‖
      ≤(∏a∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (d a) (A.M a))*((H f)^desired)⁻¹:=by
  intro held
  exact measured R d A file station axes held
    (read j f K deep openJ height berth fk cut A allSlots roots u top uj firstOpen lastOpen)
    one E refs fare s desired exposure

end YM.Integration.WilsonSeparatedPrefixPanelReturn
end
