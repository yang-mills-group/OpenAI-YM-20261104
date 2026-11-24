import YM.Integration.WilsonSeparatedPrefixMovingInvoice
import YM.Integration.WilsonIndependentMovingRosterBirthReceipt

/-! One finite-stage financial appointment for the old near roster, the
authentic exterior column, the first exterior join and the older scalar. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMovingRosterInvoice
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar WilsonSeparatedPrefixMovingWages
open WilsonSeparatedPrefixMovingInvoice (credit salary desk)
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{e n:ℕ}{E W V:Credit}

def entry (H:Hol G)(F:SealR G)(e k u a:ℕ)(prior terminal E W V:Credit):Credit:=
  (((terminal.prodC prior).prodC (effort G e k u a E W)).prodC (label H F e (u+a) E W V))

def charge (Q:Fin (n+1)→SealR G)(F:SealR G)(X:Herit Q)(Y:F.Rider)(e u a:ℕ)(r g DF:ℝ)(B:Fin (n+1)→ℝ):ℝ:=
  ((16*r)^u*(g⁻¹)^a*coupon F Y e (u+a) r DF)*
    ((9:ℝ)^(u+a)*WilsonIndependentMovingRosterBirth.charge Q X e B)

theorem positive (Q:Fin (n+1)→SealR G)(F:SealR G)(X:Herit Q)(Y:F.Rider)(e u a:ℕ)(r g DF:ℝ)
    (B:Fin (n+1)→ℝ)(rad:0 ≤ r)(apart:0 < g)(fin:0 ≤ DF)(stock:∀i,0 ≤ B i):
    0 ≤ charge Q F X Y e u a r g DF B:=by
  have isPaid (A:SealR G)(v:A.Rider):0 ≤ WilsonSeparatedPrefixMovingOwnDate.fee A e v:=by
    unfold WilsonSeparatedPrefixMovingOwnDate.fee;positivity
  have near:0 ≤ WilsonIndependentMovingRosterBirth.charge Q X e B:=
    Finset.prod_nonneg fun i _=>mul_nonneg (stock i) (isPaid (Q i) (X i))
  have far:0 ≤ coupon F Y e (u+a) r DF:=by have hy:=isPaid F Y;unfold coupon;positivity
  unfold charge;positivity

theorem original (R:Realm G (e+1) E)(F:SealR G)(Y:F.Rider)(ψ:Rarity F.D)(prior terminal:Credit)
    (k u a older i j:ℕ)(live:R.anchor ≤ older)(start:older ≤ i)(next:i ≤ j)
    (x y radius gap DF:ℝ)(cap:radiusH ψ x y ≤ radius)(gpos:0 < gap)(paid:Amplitude ψ DF):
    let Z:=epoch R older (j+1)
    let price:=R.cash (priceWG G e k u a E W) i*((16*radius)^u*(((ll R.draws i).L.val:ℝ)/gap)^a)
    let returned:=unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a) F Y ψ Z x y DF
    terminal.buy (epoch R older i)*prior.buy Z*price*returned ≤
      (entry H F e k u a prior terminal E W V).buy Z*((16*radius)^u*(gap⁻¹)^a*coupon F Y e (u+a) radius DF):=by
  intro Z price returned
  have p:=((WilsonSeparatedPrefixMovingInvoice.credit R terminal older i (j+1) live start (by omega)).mul
      (WilsonSeparatedPrefixMovingInvoice.credit R prior older (j+1) (j+1) live (by omega) le_rfl)).mul
    (salary (W:=W) R older i (j+1) k u a live start (by omega) radius gap
      ((zero_le_one.trans (fieldCap ..)).trans cap) gpos)
  have all:=p.mul (desk (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) F Y ψ (u+a) Z x y radius DF
    (window R older i (j+1) live start (by omega)).1 cap paid)
  simpa only [one_mul,entry] using all.grant

end YM.Integration.WilsonIndependentMovingRosterInvoice
