import YM.Integration.WilsonIndependentConditionedBankTable
import YM.Integration.WilsonIndependentConditionedPivotTailWing

/-! A zero-radius receiving branch of the very same high-moment course
measures the full scalar of two pure public directions. The price exposes
one engineering power per direction, before the fitted matrix inverse. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 360000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramPrices
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile (Income charge occupied)
open WilsonIndependentConditionedBankTable (direction measure)
open WilsonIndependentMatchedPivotSeat (axis)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{e k u:ℕ}{E W V U:Credit}

private theorem zeroRadius {Y:Era G ℝ}{h:ℕ}{p:ProfileW}{A:ℝ}
    (paid:Income Y h e 0 p A)(positive:0 ≤ A):
    Flush e u 0 Y A:=by
  refine ⟨positive,fun i hi r _=>?_⟩
  have f:Rent p 0 (Y.2 i r) A:=(paid.2 0 le_rfl i r hi).paid
  have eqn:(quoteT p 0 : (Fin r→YForest G)→ℝ)=hedge 0 0 u:=by
    funext a
    simp only [quoteT,hedge,autumn,pow_zero,zero_mul,add_zero,one_pow]
  change Award _ (hedge 0 0 u) A
  rw [←eqn]
  exact f

def profile {d:ℕ}(φ:Rarity d)(y B:ℝ):ℝ:=(5*radiusH φ 1 y)^4*B

def rate (H:Hol G)(Q:SealR G)(e:ℕ)(E W V:Credit):Credit:=(polarBill H Q.ans Q.path e 0 E W V).choose

private theorem offered {Q:SealR G}{R:Realm G (e+1) E}(sold:PassportC H R Q W V)
    (m K N:ℕ)(live:R.anchor ≤ m)(cut:m ≤ K)(vac:K ≤ N)(Z:ℝ)(room:Compar R.draws.S R.y m K ≤ Z)
    (φ:Rarity Q.D)(y:ℝ)(o:CellR)(i:Alma Q.F)(B:ℝ)(paid:Amplitude φ B)(clock:1 ≤ Z):
    let x:=paceT R.draws.S m K
    let C:=rate H Q e E W V
    let salary:=(x^Q.h)⁻¹*(C.buy Z*profile φ y B)
    Income (direction R Q m K N φ y o i) Q.h e 0 (OrbP (ll R.draws K) φ x y o) salary ∧ 0 ≤ salary:=by
  intro x C salary
  have b:=WilsonSeparatedPrefixMovingOwnDate.column sold m K N 0 live cut vac Z room
    (axis i 0) φ y o (ll R.draws K) B paid
  have gain:0 ≤ C.buy Z:=zero_le_one.trans (C.purchase clock)
  have f0:=WilsonIndependentConditionedPivotTailSchool.unitFee Q i 0 (Nat.zero_le e)
  have radius:radiusH φ x y ≤ radiusH φ 1 y:=by
    dsimp only [radiusH]
    rw [abs_of_pos (pace_pos ..),abs_one]
    linarith only [pace_le R.draws.S cut]
  have f1:0 ≤ radiusH φ x y:=zero_le_one.trans (fieldCap ..)
  have dx:0 < x:=pace_pos ..
  have price:charge φ 0 Q.h x y (C.buy Z*WilsonSeparatedPrefixMovingOwnDate.fee Q e (axis i 0)) B ≤ salary:=by
    rw [WilsonSeparatedPrefixMovingOwnDate.units,f0]
    simp only [pow_zero,one_mul,mul_one]
    unfold salary profile
    rw [show C.buy Z*((5*radiusH φ 1 y)^4*B)=(5*radiusH φ 1 y)^4*(B*C.buy Z) by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (by norm_num) f1) (by linarith only [radius]) _) (mul_nonneg paid.1 gain))
      (inv_nonneg.mpr (pow_nonneg dx.le _))
  refine ⟨⟨b.1,fun t ht j r hj=>(b.2 t ht j r hj).stepX price ht⟩,?_⟩
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg dx.le _)) (mul_nonneg gain (mul_nonneg (by positivity) paid.1))

theorem original (H:Hol G)(Q₁ Q₂:SealR G)(k e u:ℕ)(E W V U:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E),PassportC H R Q₁ W V → PassportC H R Q₂ W V →
      Dormitory R (k+k) u U → Q₁.h+Q₂.h ≤ k+k →
      ∀(host m K N:ℕ),R.anchor ≤ host → host ≤ m → m ≤ K → K ≤ N →
      ∀(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(B B' y:ℝ)(o:CellR),Amplitude φ B → Amplitude ψ B' →
      ∀(i:Alma Q₁.F)(j:Alma Q₂.F)(ω:Fin 0→YForest G),
      let x:=paceT R.draws.S m K
      let A:=C.buy (epoch R host K)*(x^(Q₁.h+Q₂.h))⁻¹*
        (coinMat (Q₁.h+Q₂.h) e*profile φ y B*profile ψ y B')
      let bank:=embed (measure R Q₁ Q₂ k m K N host φ ψ y o 0 ω i j)
      (∀q ≤ e,‖coeff q bank‖ ≤ A) ∧ ∀q ≤ e,belt q bank ≤ ((q+1:ℕ):ℝ)*A:=by
  obtain ⟨carry,hear⟩:=waveSeen G (k+k) e u E U
  let C₁:=rate H Q₁ e E W V
  let C₂:=rate H Q₂ e E W V
  refine ⟨carry.prodC (C₁.prodC C₂),?_⟩
  intro R first second real depth host m K N live older cut vac φ ψ B B' y o hp hq i j ω x A bank
  let Z:=epoch R host K
  have dates:=window R host m K live older cut
  have held:=window R host host K live le_rfl (older.trans cut)
  obtain ⟨L,lo⟩:=offered first m K N (live.trans older) cut vac Z dates.2.2.1 φ y o i B hp dates.1
  obtain ⟨T,to'⟩:=offered second m K N (live.trans older) cut vac Z dates.2.2.1 ψ y o j B' hq dates.1
  have product:=occupied L T
  let P:=agateV (direction R Q₁ m K N φ y o i) (direction R Q₂ m K N ψ y o j)
  have auth:Auth (k+k) P:=product.1.tall depth
  have escort:Escort R host K (fun _=>0):=by
    refine ⟨live,older.trans cut,fun _ _ _=>le_rfl,fun _ _ _=>zero_le_one,?_⟩
    intro t _ _
    simp only [thinLevel,zero_div,le_refl]
  have paid:=zeroRadius (u:=u) product (mul_nonneg (mul_nonneg (coinMat_nn ..) lo) to')
  have received:=hear R real host K (fun _=>0) K N N _ (max 0 (R.tempC K K)) Z escort held.2.2.2
    le_rfl vac vac (le_max_right _ _) P P (Fringed.same paid auth (le_max_left _ _))
  have tier (q:ℕ)(grade:q ≤ e):‖coeff q bank‖ ≤ A:=by
    have income:=WilsonIndependentMatchedCoverJoined.unit received.f_l q grade ω
    simp only [bank,embed,coeff_map,WilsonIndependentConditionedBankTable.measure,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]
    have cast (t:ℝ):‖algebraMap ℝ ℂ t‖=‖t‖:=by simp
    rw [cast]
    apply income.trans_eq
    dsimp only [A,Z,C₁,C₂,x]
    rw [Credit.products,Credit.products,pow_add,_root_.mul_inv_rev]
    ring
  refine ⟨tier,fun q hq'=>?_⟩
  calc
    _ ≤ ∑j∈range (q+1),A:=by
      exact sum_le_sum fun j hj=>tier j ((Nat.le_of_lt_succ (mem_range.mp hj)).trans hq')
    _=_:=by simp

end YM.Integration.WilsonIndependentConditionedGramPrices
