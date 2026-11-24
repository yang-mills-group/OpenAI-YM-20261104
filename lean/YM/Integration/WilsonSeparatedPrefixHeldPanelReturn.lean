import YM.Integration.WilsonSeparatedPrefixPanelReturn
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldMasterUpper

/-! Apply the funded public master at its genuine clear and radial readers with every occupation retained. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixHeldPanelReturn
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
open WilsonOriginalMicroscopicEntranceHeldMasterUpper (ReadAt)
open WilsonOriginalMicroscopicEntranceHeldMasterRead (ReadingAt)
open WilsonSeparatedPrefixPanelReturn (trueFace independentFace)
open private cutoff planted from YM.Integration.WilsonSeparatedPrefixPanelReturn
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open PertExtension PertExtension.LatticePT
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per f K u:ℕ}
local notation "C" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin n)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
variable (A:Panel R d N per f K fk cut requested power t B)

theorem measured (file:Filed R d K)(station:A.slot=file.station)(axes:A.axis=file.A N per)(held:u≤f)
    (W:Config G ((C).side u per))(sale:ReadingAt R d A held W)(one:∀a,1≤A.M a)(E:Fin n→ℕ)(refs:∀a b,b≤d a→(C).ref b≤N)
    (fare:∀a,Next.Rank.Spindle.paid (C) (d a) f N per (A.names a)≤A.M a*(H f)^(E a))
    (s:(J).Mode)(desired:ℕ)(exposure:desired+∑a∈s.val,E a≤requested):
    ‖readingAt R (N:=N) (credit (C) N per 0 (trueFace R d A s) K cut) (held.trans fk) W-
      readingAt R (N:=N) (numerator R N per K (independentFace R d A file s)) (held.trans fk) W‖
      ≤(∏a∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (d a) (A.M a))*((H f)^desired)⁻¹:=by
  let err:=readingAt R (N:=N) (credit (C) N per 0 (trueFace R d A s) K cut) (held.trans fk) W-
      readingAt R (N:=N) (numerator R N per K (independentFace R d A file s)) (held.trans fk) W
  have nc:Continuous (trueFace R d A s):=continuous_finsetProd _ fun _ _=>(C).continuousO _ _ _ _ _
  have kc:Continuous (independentFace R d A file s):=continuous_finsetProd _ fun a _=>
      continuous_const.add (((C).localSection (d a)).continuous_places _ _)
  have nz:(∏a∈s.val,(charged R d A a:ℂ))≠0:=prod_ne_zero_iff.mpr fun a _=>Complex.ofReal_ne_zero.mpr
    (WilsonReflectedPublicCommonDose.positive ..).ne'
  obtain ⟨balance,price⟩:=sale s
  have earned:=WilsonSeparatedPrefixHeldValue.restored R W cut (held.trans fk) nc kc _ nz
    (cutoff R d A s) (planted R d A file station axes s) (balance ▸ price)
  have paid:‖err‖≤(∏v∈s.val,‖(charged R d A v:ℂ)‖)⁻¹*((H f)^requested)⁻¹:=by simpa only [norm_prod] using earned
  have smaller:((H f)^requested)⁻¹≤((H f)^(desired+∑a∈s.val,E a))⁻¹:=
    inv_anti₀ (pow_pos (zero_lt_one.trans_le ((C).path.levels.fits.delayed f).le) _)
      (pow_le_pow_right₀ ((C).path.levels.fits.delayed f).le exposure)
  exact WilsonSeparatedPrefixActualDose.original R d A.M E one (fk.trans cut) A.names A.home A.sensors A.stamps
    A.enrolled refs fare s.val desired err (paid.trans (mul_le_mul_of_nonneg_left smaller
      (inv_nonneg.mpr (prod_nonneg fun _ _=>norm_nonneg _))))

theorem original {m apron reserve first degree target:ℕ}
    (read:ReadAt R d m N per apron requested t reserve power degree target B first)
    (openJ:m+1≤u)(deep:first≤u)(height:u≤f)(berth:K=WilsonInvariantActionPosition.berth R reserve f)
    (allSlots:∀v,first≤A.slot v)(path:∀a,Unit×((Fin n)×Bool)→Site ((C).side a per))
    (large:5≤((C).path.rep N per f).p.B)
    (apart:∀v w:Fin n,v≠w→((C).path.rep N per f).p.B^2+1 ≤ separation (A.loc v) (A.loc w))
    (ap:(C).S.a u/(C).S.a f≤(H f)^apron)(top:path f=(A.loc∘Prod.fst)∘Prod.snd)
    (step:∀h,u≤h→h<f→path h=((C).path.levels.clock.op h per).ratio.parent ∘ path (h+1))
    (file:Filed R d K)(station:A.slot=file.station)(axes:A.axis=file.A N per)
    (one:∀a,1≤A.M a)(E:Fin n→ℕ)(refs:∀a b,b≤d a→(C).ref b≤N)
    (fare:∀a,Next.Rank.Spindle.paid (C) (d a) f N per (A.names a)≤A.M a*(H f)^(E a))
    (s:(J).Mode)(desired:ℕ)(exposure:desired+∑a∈s.val,E a≤requested):
    let road:=height.trans fk
    let paid:=fun W=>‖readingAt R (N:=N) (credit (C) N per 0 (trueFace R d A s) K cut) road W-
      readingAt R (N:=N) (numerator R N per K (independentFace R d A file s)) road W‖
      ≤(∏a∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (d a) (A.M a))*((H f)^desired)⁻¹
    (∀W:Config G ((C).side u per),flags ((C).path.rep N per u).p.threshold W=∅ →
      WilsonOriginalMicroscopicEntranceHeldHalo.spring R u N per W≤2 → paid W) ∧
    ∀D a,a∈Push.Local.tests ((C).labels.level degree) → ∀k≤D,
      paid (WilsonCapturedPrimaryWeakTrialRadial.field R degree N per u target D a k):=by
  intro road paid
  have hearing:=read u f K openJ deep height berth fk cut A allSlots path large apart ap top step
  have buy(W:Config G ((C).side u per))(sold:ReadingAt R d A height W):paid W:=
    measured R d A file station axes height W sold one E refs fare s desired exposure
  exact ⟨fun W clear small=>buy W (hearing.1 W clear small),
    fun D a ha k hk=>buy _ (hearing.2 D a ha k hk)⟩

end YM.Integration.WilsonSeparatedPrefixHeldPanelReturn
end
