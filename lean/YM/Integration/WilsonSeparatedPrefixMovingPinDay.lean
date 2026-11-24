import YM.Integration.WilsonSeparatedPrefixMovingPinController
import YM.Integration.WilsonIndependentMovingRosterRejoin
import YM.Integration.WilsonIndependentMovingRosterContact
import YM.Integration.WilsonIndependentMovingRosterInvoice
import YM.Integration.WilsonIndependentMovingRosterBirthCalendar

/-! A genuinely deposited earlier joint near row meets the moving field
under the same dated independent law and is heard by the named older scalar. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonSeparatedPrefixMovingPinDay
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingPairSector (current vacant)
open WilsonIndependentMovingRosterRejoin (stored)
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open WilsonSeparatedPrefixMovingPinController (Sites collected)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}

def crossed {u e:ℕ}{E:Credit}(R:Realm G (e+1) E)(canvas:Sites G e u)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)(i j:ℕ):ℝ:=
  if i<j then
    let far:=current R F ψ Y t (i+1) N (y/paceT R.draws.S m t) o
    (collected R canvas (F.h+capP Q) N i older
      (JoinGap R.draws R.paid i N F.h (capP Q) far (WilsonIndependentMovingRosterRejoin.stored R Q φ X o y m i j N))).2 q 0 ω
  else 0

private lemma bounded {D:ℕ}(φ:Rarity D){x y v:ℝ}(lo:0 ≤ x)(hi:x ≤ 1)(fits:φ.radius+|y|+1 ≤ v):
    radiusH φ x y ≤ v:=by unfold radiusH;rw [abs_of_nonneg lo];linarith only [hi,fits]

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(F:SealR G)(k e u target:ℕ)(pos:0 < target)
    (E W V Sn Dn Do:Credit):
    let a:=F.h+(u+target)
    ∃shape chron:Credit,∀(R:Realm G (e+1) E)(canvas:Sites G e u)(_per:SpringD R k u a W)
      (_near:SpringD R (capP Q) (u+a) (capP Q+(u+a+2)) Sn)(_dorm:Dormitory R (capP Q) (u+a) Dn)
      (_terminal:Dormitory R (F.h+capP Q) u Do)(_roster:HorizonP H R W V Q)(_far:PassportC H R F W V)
      (older t m i j N:ℕ)(_gate:R.anchor ≤ older)(_read:older ≤ t)(_home:t ≤ m)(_fine:m ≤ i)(_birth:i < j)
      (_top:j < N)(_capacity:F.h+capP Q ≤ k)(φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)
      (o:CellR)(y rad inner outer v DF:ℝ)(B:Fin (n+1)→ℝ),
      let T:=paceT R.draws.S m t
      let x:=paceT R.draws.S m (i+1)
      let z:=paceT R.draws.S m (j+1)
      let Z:=epoch R older (j+1)
      let ticket:=shape.buy (WilsonIndependentMovingRosterBirthCalendar.room rad inner y)*
        WilsonIndependentMovingRosterInvoice.charge Q F X Y e u a v outer DF B
      0 < inner → 0 < outer → (∀s,Amplitude (φ s) (B s)) → Amplitude ψ DF → (∀s,(φ s).radius ≤ rad) →
      (∀s b,s≠b→ClearDay (φ s) (φ b) inner) →
      (∀p∈tsupport ψ.ψ.val,T*outer+1+|y| ≤ ‖T • p‖) → 2+2*|y| ≤ v → ψ.radius+|y/T|+1 ≤ v →
      ∀q ≤ e,∀ω:Fin 0→YForest G,
        ‖crossed R canvas Q F φ ψ X Y o y t m older N q ω i j‖≤
          ((T^target)⁻¹*ticket)*chron.buy Z*(x*z^2):=by
  intro a
  obtain ⟨C,carried⟩:=WilsonIndependentMovingRosterBirthCalendar.original H Q E W V Sn Dn e (u+a) 2
  obtain ⟨D,listen⟩:=WilsonSeparatedPrefixMovingPinController.earlier G (F.h+capP Q) e u E Do
  let chrono:=WilsonIndependentMovingRosterInvoice.entry H F e k u a C D E W V
  refine ⟨C,chrono,?_⟩
  intro R canvas per near dorm terminal roster far older t m i j N gate read home fine birth top capacity φ ψ X Y o y
    rad inner outer v DF B T x z Z ticket innPos outPos amps ampf fits apart away box fbox q hq ω
  have om:=read.trans home
  have edge:i < N:=by omega
  have xPos:0 < x:=pace_pos ..
  have zPos:0 < z:=pace_pos ..
  have Tpos:0 < T:=pace_pos ..
  have xSmall:x ≤ 1:=pace_le R.draws.S (by omega)
  have big:1 ≤ T:=pace_ge R.draws.S home
  have olderCap:0 ≤ v:=by linarith only [box,abs_nonneg y]
  let geo:=WilsonIndependentMovingRosterBirthCalendar.room rad inner y
  have geometry:1 ≤ geo:=le_max_left ..
  let nearFee:=WilsonIndependentMovingRosterBirth.charge Q X e B
  have paidNear:0 ≤ nearFee:=by
    apply Finset.prod_nonneg
    intro s _
    exact mul_nonneg (amps s).1 (by unfold WilsonSeparatedPrefixMovingOwnDate.fee;positivity)
  have geoPos:0 ≤ C.buy geo:=zero_le_one.trans (C.purchase geometry)
  have billNonneg:0 ≤ ticket:=mul_nonneg geoPos
    (WilsonIndependentMovingRosterInvoice.positive Q F X Y e u a v outer DF B olderCap outPos ampf.1 (fun s=>(amps s).1))
  have Zpos:1 ≤ Z:=(window R older i (j+1) gate (by omega) (by omega)).1
  let P:=ll R.draws i
  let locator:=WilsonSeparatedPrefixMovingLocator.booked y o
  let bank:=stored R Q φ X o y m i j N
  let exterior:=current R F ψ Y t (i+1) N (y/T) o
  let paired:=JoinGap R.draws R.paid i N F.h (capP Q) exterior bank
  let wage:=(9:ℝ)^(u+a)*(C.buy Z*z^2*(C.buy geo*nearFee))
  let farFee:=unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a) F Y ψ Z (x/T) (y/T) DF
  let geomPrice:=(16*v)^u*((P.L.val:ℝ)/outer)^a
  have xt:0 ≤ x/T:=div_nonneg xPos.le Tpos.le
  have smallT:x/T ≤ 1:=div_le_one_of_le₀ (xSmall.trans big) Tpos.le
  have enter:=carried R roster near dorm older m i j N φ X B rad inner y o gate om fine birth top
    innPos amps fits apart
  have income:Income bank (capP Q) e (u+a) (OrbP P locator x y o) wage:=enter.2.2
  have ck:Compar R.draws.S R.y t (i+1) ≤ Z:=
    (compar_age R.draws.S R.y t (by omega:i+1 ≤ j+1)).trans
      (window R older t (j+1) gate read (by omega)).2.2.1
  have rate:0 ≤ (T^target)⁻¹:=inv_nonneg.mpr (pow_nonneg Tpos.le _)
  have crPos:0 ≤ chrono.buy Z:=zero_le_one.trans (chrono.purchase Zpos)
  by_cases present:(VisitsT ψ (x/T) (y/T) o).Nonempty
  · have same:x*(P.L.val:ℝ)=paceT R.draws.S m i:=pace_step ..
    have stepSmall:paceT R.draws.S m i ≤ 1:=pace_le _ fine
    have Pcap:radiusH locator (x*(P.L.val:ℝ)) y ≤ v:=by
      rw [same];exact (WilsonSeparatedPrefixMovingLocator.paid _ y o (pace_pos ..).le stepSmall).trans box
    have Fcap:radiusH ψ (x*P.L.val/T) (y/T) ≤ v:=by
      rw [same];exact bounded ψ (div_nonneg (pace_pos ..).le Tpos.le)
        (div_le_one_of_le₀ (stepSmall.trans big) Tpos.le) fbox
    have sale:=WilsonIndependentMovingRosterContact.original R F (capP Q) k u a target 0 (u+target) 0
      rfl (by dsimp only [a];omega) per far t m i N (gate.trans read) home fine edge capacity bank locator ψ Y
      y outer v Z wage DF o income ck ampf outPos (WilsonSeparatedPrefixMovingLocator.site x y o xPos)
      (WilsonSeparatedPrefixMovingLocator.separated ψ T outer y o away) Pcap Fcap present
    have ret:Auth (F.h+capP Q) paired ∧ Flush e u (paceT R.draws.S m i) paired
        (R.cash (priceWG G e k u a E W) i*(((T^target)⁻¹*x^(u+target)*geomPrice)*(farFee*wage))):=by
      change Auth (F.h+capP Q) paired ∧ Flush e u (x*P.L.val) paired
        (R.cash (priceWG G e k u a E W) i*(((T^target)⁻¹*(T^0)⁻¹*x^(u+target)*geomPrice)*(farFee*wage))) at sale
      simpa only [same,pow_zero,inv_one,mul_one] using sale
    have heard:=listen R canvas terminal older m i N gate om fine edge.le paired ret.1 _ ret.2 q hq ω
    have receipt:=WilsonIndependentMovingRosterInvoice.original (H:=H) (W:=W) (V:=V) R F Y ψ C D k u a
      older i j gate (by omega) birth.le (x/T) (y/T) v outer DF (bounded ψ xt smallT fbox) outPos ampf
    have xRefund:x^(u+target) ≤ x:=by
      simpa only [pow_one] using pow_le_pow_of_le_one xPos.le xSmall (show 1 ≤ u+target by omega)
    let extra:=(T^target)⁻¹*x^(u+target)*z^2*((9:ℝ)^(u+a)*(C.buy geo*nearFee))
    have extraPos:0 ≤ extra:=by dsimp only [extra];positivity
    have package:=mul_le_mul_of_nonneg_right receipt extraPos
    rw [crossed,if_pos birth]
    refine heard.trans ?_
    calc
      _ = (D.buy (epoch R older i)*C.buy Z*(R.cash (priceWG G e k u a E W) i*geomPrice)*farFee)*extra:=by
        dsimp only [wage,extra];ring
      _ ≤ _:=package
      _ = (((T^target)⁻¹*ticket)*chrono.buy Z)*x^(u+target)*z^2:=by
        dsimp only [extra,ticket,chrono,geo,nearFee,WilsonIndependentMovingRosterInvoice.charge];ring
      _ ≤ (((T^target)⁻¹*ticket)*chrono.buy Z)*x*z^2:=by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left xRefund (mul_nonneg (mul_nonneg rate billNonneg) crPos))
          (sq_nonneg z)
      _ = _:=by ring
  · have vacantField:exterior=0:=by
      apply WilsonSeparatedPrefixMovingPairSector.vacant
      simpa only [WilsonSeparatedPrefixMovingUnformed.rulers R.draws.S t m (i+1)] using present
    have none:=WilsonSeparatedPrefixMovingPinController.vacant R canvas older i N F.h (capP Q) (om.trans fine) edge
      exterior bank (Or.inl vacantField)
    rw [crossed,if_pos birth]
    have noCash:=congrArg (fun U:Era G ℝ=>U.2 q 0 ω) none
    change ‖(collected R canvas (F.h+capP Q) N i older paired).2 q 0 ω‖ ≤ _
    rw [noCash];change ‖(0:ℝ)‖ ≤ _
    rw [norm_zero];positivity

end YM.Integration.WilsonSeparatedPrefixMovingPinDay
