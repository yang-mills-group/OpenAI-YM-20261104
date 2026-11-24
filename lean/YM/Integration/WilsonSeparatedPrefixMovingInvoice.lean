import YM.Integration.WilsonSeparatedPrefixMovingWages
/-! A finite product of dated payrolls on one regulator, preserving the
ordinary salaries of its three actual inputs. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingInvoice
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar WilsonSeparatedPrefixMovingWages
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open scoped BigOperators Topology Classical

variable {G:Gauge}{H:Hol G}{e u a:ℕ}{E W V:Credit}

structure Earned (Z:ℝ)(C:Credit)(actual dose:ℝ):Prop where
  floor:0 ≤ actual
  grant:actual ≤ C.buy Z*dose

lemma Earned.mul {Z x y a b:ℝ}{C D:Credit}(P:Earned Z C x a)(Q:Earned Z D y b):
    Earned Z (C.prodC D) (x*y) (a*b):=by
  refine ⟨mul_nonneg P.floor Q.floor,?_⟩
  have fee:=mul_le_mul P.grant Q.grant Q.floor (P.floor.trans P.grant)
  rw [Credit.products];exact fee.trans_eq (by ring)

lemma constant (Z c:ℝ)(good:0≤c):Earned Z Credit.unit c c:=by
  refine ⟨good,?_⟩;simp [Credit.unit,Credit.buy]

lemma desk (Q:SealR G)(X:Q.Rider)(φ:Rarity Q.D)(u:ℕ)(Z x y rad B:ℝ)
    (opened:1 ≤ Z)(cap:radiusH φ x y ≤ rad)(fee:Amplitude φ B):
    Earned Z (label H Q e u E W V)
      (unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u) Q X φ Z x y B) (coupon Q X e u rad B):=by
  refine ⟨?_,?_⟩
  · have initial:0≤WilsonSeparatedPrefixMovingOwnDate.fee Q e X:=by unfold WilsonSeparatedPrefixMovingOwnDate.fee;positivity
    have real:0≤(polarBill H Q.ans Q.path e u E W V).choose.buy Z:=zero_le_one.trans (Credit.purchase _ opened)
    have b:=fee.1
    unfold unitFee;positivity
  · rw [mul_comm];exact wholeLabel Q X φ Z x y rad B opened cap fee

lemma salary (R:Realm G (e+1) E)(t i j k u a:ℕ)(live:R.anchor ≤ t)(base:t ≤ i)(budget:i ≤ j)
    (rad gap:ℝ)(h:0 ≤ rad)(pos:0 < gap):
    Earned (epoch R t j) (effort G e k u a E W)
      (R.cash (priceWG G e k u a E W) i*((16*rad)^u*(((ll R.draws i).L.val:ℝ)/gap)^a))
      ((16*rad)^u*gap⁻¹^a):=by
  refine ⟨?_,native R t i j k live base budget rad gap h pos⟩
  have actual:0≤R.cash (priceWG G e k u a E W) i:=zero_le_one.trans (Credit.purchase _ (R.depth i (live.trans base)))
  positivity

lemma credit (R:Realm G (e+1) E)(C:Credit)(t i j:ℕ)(live:R.anchor ≤ t)(base:t ≤ i)(budget:i ≤ j):
    Earned (epoch R t j) C (C.buy (epoch R t i)) 1:=by
  have opened:1≤epoch R t i:=(window R t i i live base le_rfl).1
  refine ⟨zero_le_one.trans (C.purchase opened),?_⟩
  rw [mul_one];apply C.elder opened
  unfold WilsonSeparatedPrefixMovingCalendar.epoch;linarith only [scales R.draws.S budget]

def entry (H:Hol G)(A B F:SealR G)(e k u a ai:ℕ)(carry finish E W V:Credit):Credit:=
  ((((finish.prodC carry).prodC (effort G e k u a E W)).prodC (label H F e (u+a) E W V)).prodC
    ((effort G e k (u+a) ai E W).prodC ((label H A e (u+a+ai) E W V).prodC
      (label H B e (u+a+ai) E W V))))

theorem original (R:Realm G (e+1) E)(A B F:SealR G)(carry finish:Credit)(k u a ai t i j:ℕ)
    (live:R.anchor ≤ t)(base:t ≤ i)(next:i ≤ j)(X:A.Rider)(Y:B.Rider)(E₀:F.Rider)
    (φ:Rarity A.D)(ψ:Rarity B.D)(far:Rarity F.D)(w x y v r z DA D_B DF c g:ℝ)
    (cp:0<c)(gp:0<g)(pA:Amplitude φ DA)(pB:Amplitude ψ D_B)(pF:Amplitude far DF)
    (boxA:radiusH φ x y ≤ r)(boxB:radiusH ψ x y ≤ r)(boxF:radiusH far w v ≤ z):
    let Z:=epoch R t (j+1)
    let M:ℝ:=(ll R.draws j).L.val
    let L:ℝ:=(ll R.draws i).L.val
    let inner:=R.cash (priceWG G e k (u+a) ai E W) j*((16*r)^(u+a)*(M/c)^ai)*
      (unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a+ai) A X φ Z x y DA*
       unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a+ai) B Y ψ Z x y D_B)
    let outer:=R.cash (priceWG G e k u a E W) i*((16*z)^u*(L/g)^a)*
      unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a) F E₀ far Z w v DF
    let inputs:=coupon A X e (u+a+ai) r DA*coupon B Y e (u+a+ai) r D_B*coupon F E₀ e (u+a) z DF
    let tariff:=(9:ℝ)^(u+a)*(16*z)^u*(g⁻¹)^a*(16*r)^(u+a)*(c⁻¹)^ai*inputs
    finish.buy (epoch R t i)*carry.buy Z*(9:ℝ)^(u+a)*(M^(u+a))⁻¹*outer*inner ≤
      (entry H A B F e k u a ai carry finish E W V).buy Z*tariff:=by
  intro Z M L inner outer inputs tariff
  have born:t≤j:=base.trans next
  have e0:1≤Z:=(window R t i (j+1) live base (by omega)).1
  have soldF:=desk (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) F E₀ far (u+a) Z w v z DF e0 boxF pF
  have soldA:=desk (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) A X φ (u+a+ai) Z x y r DA e0 boxA pA
  have soldB:=desk (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) B Y ψ (u+a+ai) Z x y r D_B e0 boxB pB
  have sr:0≤r:=(zero_le_one.trans (fieldCap ..)).trans boxA
  have sz:0≤z:=(zero_le_one.trans (fieldCap ..)).trans boxF
  have moneyF:=salary (W:=W) R t i (j+1) k u a live base (by omega) z g sz gp
  have moneyA:=salary (W:=W) R t j (j+1) k (u+a) ai live born (by omega) r c sr cp
  have wages:=(((((credit R finish t i (j+1) live base (by omega)).mul
    (credit R carry t (j+1) (j+1) live (by omega) le_rfl)).mul moneyF).mul soldF).mul
      (moneyA.mul (soldA.mul soldB)))
  let physical:=finish.buy (epoch R t i)*carry.buy Z*outer*inner
  have refund: (M^(u+a))⁻¹≤1:=inv_le_one_of_one_le₀ (one_le_pow₀
    (show 1≤M by change 1 ≤ ((ll R.draws j).L.val:ℝ); exact_mod_cast (ll R.draws j).L.pos))
  have nonneg:0≤physical:=by
    convert wages.floor using 1
    dsimp only [physical,outer,inner];ring
  have refundFee:=mul_le_mul_of_nonneg_left refund (mul_nonneg nonneg (show (0:ℝ)≤9^(u+a) by positivity))
  have bill:=mul_le_mul_of_nonneg_right wages.grant (show (0:ℝ)≤9^(u+a) by positivity)
  calc
    _=physical*(9:ℝ)^(u+a)*(M^(u+a))⁻¹:=by dsimp only [physical];ring
    _≤physical*(9:ℝ)^(u+a):=refundFee.trans_eq (mul_one _)
    _≤_:=by
      refine Eq.trans_le ?_ (bill.trans_eq ?_)
      · dsimp only [physical,outer,inner];ring
      · dsimp only [entry,inputs,tariff];ring

end YM.Integration.WilsonSeparatedPrefixMovingInvoice
