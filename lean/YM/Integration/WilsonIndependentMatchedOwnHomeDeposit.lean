import YM.Integration.WilsonIndependentMatchedOwnHomeAxisWage
import YM.Integration.WilsonIndependentMatchedOwnHomeRoster
import YM.Integration.WilsonSeparatedPrefixMovingPinWallet
import YM.Integration.WilsonSeparatedPrefixMovingPinHearing
import YM.Integration.WilsonSeparatedPrefixMovingPairSector

/-! Attach the actual reissued far pivot to an earlier near deposit on its
own old vacuum, before the joint marked return and at the same held pin. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOwnHomeDeposit
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMatchedCoverProfile (Income)
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{e k:ℕ}{E W V A L:Credit}

private theorem angular {P:Era G ℝ}{d:ℕ}{v:ProfileW}{money:ℝ}(sale:Income P d e 0 v money):
    Flush e 0 1 P money:=by
  have cap:=sale.2 0 le_rfl
  refine ⟨((cap 0 0 (Nat.zero_le _)).paid).C,?_⟩
  intro i hi r _
  exact (cap i r hi).paid.less (fun _=>by simp only [Mer.quoteT,Shard.hedge,Shard.autumn,pow_zero];rfl) (Shard.hedge_nn zero_le_one)

def price (Q:SealR G)(k e:ℕ)(C B terminal polar:Credit)(S:Schedule)(w:ℕ→ℝ)
    (t m K older:ℕ)(φ:Rarity Q.D)(y amp:ℝ):ℝ:=
  terminal.buy (w older+2*(S.scale K-S.scale older))*
    (coinMat (Q.h+k) e*(5*radiusH φ (paceT S t K) (y/paceT S m t))^4*amp*
    polar.buy (Compar S w t K)*(Fintype.card (Alma Q.F):ℝ)^2*(e+1)*
    C.buy (Compar S w t m)*B.buy (w m))

private theorem settle (T δ:ℝ)(h ex:ℕ)(ht:0<T)(dx:0<δ)(u v house amp c d n g B cost:ℝ):
    (T^h)⁻¹*(u*(v*(((δ/T)^h)⁻¹*(house*(amp*(c*(d*n*T^h*g*B)))))*(δ^(h+ex)*cost)))=
    T^h*δ^ex*(u*(v*house*amp*c*d*n*g*B))*cost:=by
  rw [div_pow,inv_div,div_eq_mul_inv,pow_add]
  calc
    _ = (((T^h)⁻¹*T^h)*((δ^h)⁻¹*δ^h))*(T^h*δ^ex*(u*(v*house*amp*c*d*n*g*B))*cost):=by ring
    _ = _:=by rw [inv_mul_cancel₀ (pow_ne_zero h ht.ne'),inv_mul_cancel₀ (pow_ne_zero h dx.ne'),one_mul,one_mul]

theorem original (H:Hol G)(Q:SealR G)(k e:ℕ)(E W V A L:Credit):
    ∃C B terminal:Credit,∀(R:Realm G (e+1) E)(_far:AheadT H R W V Q A)
    (_room:Dormitory R (Q.h+k) 0 L)(older t m K N:ℕ),R.anchor ≤ older → older ≤ t → t ≤ m → m ≤ K → K ≤ N →
    ∀(φ:Rarity Q.D)(amp y:ℝ)(z:CellR)(a:Alma Q.F)(pin:Cover)(b extra:ℕ)(D:Era G ℝ)(need:ℝ),
    Amplitude φ amp → Auth k D → Flush e 0 1 D ((paceT R.draws.S m K)^(Q.h+extra)*need) →
    ∀j ≤ e,∀ω:Fin 0→YForest G,
    let T:=paceT R.draws.S m t
    let far:=current R Q φ (PermuteLens R.draws R.paid Q N t (brought R.draws R.paid Q N t m (axis Q a))) t K N (y/T) z
    let paid:=price Q k e C B terminal (polarBill H Q.ans Q.path e 0 E W V).choose R.draws.S R.y t m K older φ y amp
    ‖(T^Q.h)⁻¹*(hear R (Q.h+k) N b older pin K (agateV far D)).2 j 0 ω‖ ≤
      T^Q.h*(paceT R.draws.S m K)^extra*paid*need:=by
  obtain ⟨C,B,axes⟩:=WilsonIndependentMatchedOwnHomeAxisWage.original H Q e E W V A
  obtain ⟨term,transit⟩:=WilsonSeparatedPrefixMovingPinWallet.original G (Q.h+k) e E L
  refine ⟨C,B,term,?_⟩
  intro R own dorm older t m K N start before dates plant prior φ amp y z a pin b extra D need profile ok bill j hj ω T far paid
  let S:=R.draws.S
  let x:=paceT S t K
  let δ:=paceT S m K
  let Z:=Compar S R.y t K
  let α:=(polarBill H Q.ans Q.path e 0 E W V).choose
  let Y:=PermuteLens R.draws R.paid Q N t (brought R.draws R.paid Q N t m (axis Q a))
  have wt:0<T:=pace_pos ..
  have small:0<δ:=pace_pos ..
  have young:=start.trans before
  have tm:=dates.trans plant
  have idx:x=δ/T:=WilsonIndependentMatchedOwnHomeRoster.spacing S t m K
  have paidZ:1 ≤ Z:=by
    change 1 ≤ R.y t+_+_
    have mono:=scales R.draws.S tm
    have nn:=R.depth t young
    have span:0≤((K-t:ℕ):ℝ):=by positivity
    linarith only [mono,nn,span]
  have scale:0 ≤ α.buy Z:=zero_le_one.trans (α.purchase paidZ)
  have effect:0 ≤ need:=nonneg_of_mul_nonneg_right bill.1 (pow_pos small _)
  have peer:=WilsonSeparatedPrefixMovingOwnDate.column own.p t K N 0 young tm prior Z le_rfl Y φ (y/T) z (ll R.draws K) amp profile
  have farFee:=angular peer
  rw [WilsonSeparatedPrefixMovingOwnDate.units,pow_zero,one_mul] at farFee
  have pairD:=fringedMat (Fringed.same farFee peer.1 (le_refl (0:ℝ))) (Fringed.same bill ok (le_refl (0:ℝ))) zero_le_one (le_refl (Q.h+k))
  let tot:=coinMat (Q.h+k) e
  let P:=((x^Q.h)⁻¹*((5*radiusH φ x (y/T))^4*(amp*(α.buy Z*fee Q e Y))))
  have bank:Flush e 0 (paceT S K K) (agateV far D) (tot*P*(δ^(Q.h+extra)*need)):=by
    simpa only [pace_self,tot,P,δ,x,α,Z,Y,S,far,current] using pairD.f_l
  let clock:=epoch R older K
  have paidClock:=term.purchase (WilsonSeparatedPrefixMovingCalendar.window R older K K start (before.trans tm) le_rfl).1
  have h0:0 ≤ term.buy clock:=zero_le_one.trans paidClock
  have r:=(transit R dorm older K K N start (before.trans tm) le_rfl prior (agateV far D) pairD.inkV _ bank
    (WilsonPositionProgramPinnedHearthHistory.pin S b K pin) j hj ω)
  have ray:=axes R own t m N young dates (plant.trans prior) a
  let p:=(Fintype.card (Alma Q.F):ℝ)^2*(e+1)*T^Q.h*C.buy (Compar S R.y t m)*B.buy (R.y m)
  have wage:fee Q e Y≤p:=ray
  have ht:0 ≤ tot:=coinMat_nn ..
  have test:0 ≤ (5*radiusH φ x (y/T))^4:=by positivity
  have left:0≤(T^Q.h)⁻¹:=by positivity
  have xd:0<x:=pace_pos ..
  have house:=profile.1
  have re:‖(hear R (Q.h+k) N b older pin K (agateV far D)).2 j 0 ω‖≤term.buy clock*(tot*P*(δ^(Q.h+extra)*need)):=r
  calc
    _ = (T^Q.h)⁻¹*‖(hear R (Q.h+k) N b older pin K (agateV far D)).2 j 0 ω‖:=by rw [norm_mul,Real.norm_of_nonneg left]
    _ ≤ (T^Q.h)⁻¹*(term.buy clock*(tot*((x^Q.h)⁻¹*((5*radiusH φ x (y/T))^4*(amp*(α.buy Z*p))))*(δ^(Q.h+extra)*need))):=by
      apply mul_le_mul_of_nonneg_left (re.trans _) left
      dsimp only [P]
      gcongr
    _ = _:=by
      dsimp only [p]
      change _=T^Q.h*δ^extra*(term.buy clock*(tot*(5*radiusH φ x (y/T))^4*amp*α.buy Z*(Fintype.card (Alma Q.F):ℝ)^2*(e+1)*C.buy (Compar S R.y t m)*B.buy (R.y m)))*need
      rw [idx]
      exact settle T δ Q.h extra wt small _ _ _ _ _ _ _ _ _ _
end YM.Integration.WilsonIndependentMatchedOwnHomeDeposit
end
