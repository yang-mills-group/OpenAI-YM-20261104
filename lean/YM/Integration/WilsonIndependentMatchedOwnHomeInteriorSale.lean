import YM.Integration.WilsonIndependentMatchedOwnHomeDeposit
import YM.Integration.WilsonIndependentMatchedOwnHomePanel
import YM.Integration.WilsonIndependentConditionedHeldJoins

/-! The earned, unweighted earlier near deposit at the real moving detector.
The near and far stencils share the original finite vacuum and the terminal pin. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeInteriorSale
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentMatchedOwnHomeDeposit (price)
open WilsonIndependentMovingRosterBirth (charge)
open WilsonSeparatedPrefixMovingPinChamber (panel)
open WilsonIndependentMatchedOwnHomePanel (born)
open scoped BigOperators Classical
variable {G:Gauge}{n d:ℕ}

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(F:SealR G)(e ex:ℕ)(surplus:2 ≤ F.h+ex)
    (E W V A Sn Dn Df:Credit):
    ∃C B terminal near reach:Credit,∀(R:Realm G (e+1) E)(_roster:HorizonP H R W V Q)
    (_far:AheadT H R W V F A)(_spring:SpringD R (capP Q) 0 (capP Q+(0+(F.h+ex))) Sn)
    (_near:Dormitory R (capP Q) 0 Dn)(_joint:Dormitory R (F.h+capP Q) 0 Df)
    (older t b m K N:ℕ),R.anchor ≤ older → older ≤ t → t ≤ b → b ≤ m → m ≤ K → K ≤ N →
    ∀(α:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(a:Alma F.F)(Φ:Rarity d)(amp ampFar y room:ℝ)
    (wages:Fin (n+1)→ℝ)(o:CellR),Amplitude Φ amp → Amplitude ψ ampFar → Bough Q α (paceT R.draws.S m b) room wages →
    ∀j ≤ e,∀ω:Fin 0→YForest G,
    let T:=paceT R.draws.S m t
    let x:=paceT R.draws.S m K
    let width:=paceT R.draws.S m b
    let Y:=PermuteLens R.draws R.paid F N t (brought R.draws R.paid F N t m (axis F a))
    let pay:=price F (capP Q) e C B terminal (polarBill H F.ans F.path e 0 E W V).choose R.draws.S R.y t m K older ψ width ampFar
    let bill:=2*reach.buy (epoch R m K)*(near.buy room*charge Q X e wages)
    ‖(T^F.h)⁻¹*(panel R Q F α ψ X Y Φ y o t m b older N K j 0 ω-
      born R Q F α ψ X Y Φ y o t m b older K N j 0 ω)‖ ≤
    (5*radiusH Φ (paceT R.draws.S t b) y)^4*amp*(T^F.h*x^ex*pay*bill):=by
  obtain ⟨C,B,terminal,attach⟩:=WilsonIndependentMatchedOwnHomeDeposit.original H F (capP Q) e E W V A Df
  obtain ⟨near,reach,held⟩:=WilsonIndependentConditionedHeldJoins.original H Q e 0 (F.h+ex) surplus E W V Sn Dn
  refine ⟨C,B,terminal,near,reach,?_⟩
  intro R roster far spring quiet joint older t b m K N old date window middle plant top α ψ X a Φ amp ampFar y room wages o test outside geo j hj ω T x width Y pay bill
  let R0:=T^F.h*x^ex*pay*bill
  have wT:0<T:=pace_pos ..
  have w:(0:ℝ)<T^F.h:=pow_pos wT _
  have time:=window.trans middle
  have openM:=old.trans (date.trans time)
  let D (z:CellR):=locale z (LodeStar R.draws R.paid α X m K N width)-Ashore Q R.draws R.paid α X m K N width z
  let output (s:Cover)(z:CellR):=
    (WilsonSeparatedPrefixMovingPinHearing.hear R (F.h+capP Q) N b older s K
      (agateV (WilsonSeparatedPrefixMovingPairSector.current R F ψ Y t K N (width/T) z) (D z))).2 j 0 ω
  have paid (s:Cover)(z:CellR):‖(T^F.h)⁻¹*output s z‖≤R0:=by
    obtain ⟨leg,issued,_⟩:=held R roster spring quiet m K N openM plant top α X wages width room z geo
    have bank:Flush e 0 1 (D z) (x^(F.h+ex)*bill):=by
      convert issued using 1
      dsimp only [bill]
      ring
    exact attach R far joint older t m K N old date time plant top ψ ampFar width z a s b ex (D z) bill outside leg bank j hj ω
  have ok:0≤R0:=(norm_nonneg _).trans (paid 0 zeroC)
  have bound (s:Cover)(z:CellR):‖output s z‖≤T^F.h*R0:=by
    have low:=paid s z
    rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr w.le)] at low
    simpa only [←mul_assoc,mul_inv_cancel₀ w.ne',one_mul] using (mul_le_mul_of_nonneg_left low w.le)
  have scored:=WilsonIndependentMatchedOwnHomePanel.original R Q F α ψ X Y roster far.p Φ y o t m b older K N j 0 ω
    (openM.trans plant) (date.trans (time.trans plant)) top window amp (T^F.h*R0) test (mul_nonneg w.le ok)
    (fun s _ z=>bound s z)
  rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr w.le)]
  apply (mul_le_mul_of_nonneg_left scored (inv_nonneg.mpr w.le)).trans_eq
  calc
    _=((T^F.h)⁻¹*T^F.h)*((5*radiusH Φ (paceT R.draws.S t b) y)^4*amp*R0):=by ring
    _=_:=by rw [inv_mul_cancel₀ w.ne',one_mul]

end YM.Integration.WilsonIndependentMatchedOwnHomeInteriorSale
end
