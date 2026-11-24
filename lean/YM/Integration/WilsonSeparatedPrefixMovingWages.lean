import YM.Integration.WilsonSeparatedPrefixMovingFineDeposit
import YM.Integration.WilsonSeparatedPrefixMovingCalendar
import YM.Integration.WilsonIndependentMatchedCoverJoined

/-! Turn the dated Mer salaries into genuine fixed-order credits on a single
older clock. No exponent of the exterior distance is used for these credits. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingWages
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open scoped BigOperators Topology Classical
variable {G:Gauge}{H:Hol G}{e u a:ℕ}{E W V:Credit}

def label (H:Hol G)(Q:SealR G)(e u:ℕ)(E W V:Credit):Credit:=(polarBill H Q.ans Q.path e u E W V).choose
def coupon (Q:SealR G)(X:Q.Rider)(e u:ℕ)(radius income:ℝ):ℝ:=
  (5*radius)^4*(9^u*(income*WilsonSeparatedPrefixMovingOwnDate.fee Q e X))
def effort (G:Gauge)(e k u a:ℕ)(E W:Credit):Credit:=(priceWG G e k u a E W).prodC (E.powC a)

lemma wholeLabel (Q:SealR G)(X:Q.Rider)(φ:Rarity Q.D)(Z x y radius B:ℝ)
    (epochPos:1 ≤ Z)(cap:radiusH φ x y  ≤  radius)(profile:Amplitude φ B):
    WilsonSeparatedPrefixMovingFineFare.unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u)
      Q X φ Z x y B  ≤  coupon Q X e u radius B*(label H Q e u E W V).buy Z:=by
  have nonneg:0 ≤ WilsonSeparatedPrefixMovingOwnDate.fee Q e X:=by unfold WilsonSeparatedPrefixMovingOwnDate.fee; positivity
  have wage:0 ≤ (label H Q e u E W V).buy Z:=zero_le_one.trans (Credit.purchase _ epochPos)
  have center:0 ≤ radiusH φ x y:=zero_le_one.trans (fieldCap ..)
  change (5*radiusH φ x y)^4*(9^u*(B*((label H Q e u E W V).buy Z*WilsonSeparatedPrefixMovingOwnDate.fee Q e X))) ≤ _
  calc
    _ ≤ (5*radius)^4*(9^u*(B*((label H Q e u E W V).buy Z*WilsonSeparatedPrefixMovingOwnDate.fee Q e X))):=by
      have income:=profile.1
      gcongr
    _=_:=by unfold coupon;ring

lemma native (R:Realm G (e+1) E)(t i j k:ℕ)(gate:R.anchor ≤ t)(starts:t ≤ i)(endAt:i ≤ j)
    (rad gap:ℝ)(radPos:0 ≤ rad)(pos:0<gap):
    R.cash (priceWG G e k u a E W) i*((16*rad)^u*(((ll R.draws i).L.val:ℝ)/gap)^a) ≤ 
      (effort G e k u a E W).buy (epoch R t j)*((16*rad)^u*(gap⁻¹)^a) := by
  have w:=window R t i j gate starts endAt
  have active:=R.depth i (gate.trans starts)
  have dated: R.cash (priceWG G e k u a E W) i  ≤  (priceWG G e k u a E W).buy (epoch R t j):=
    Credit.elder _ active w.2.1
  have length:((ll R.draws i).L.val:ℝ) ≤ E.buy (epoch R t j):=
    (R.taxes i (gate.trans starts)).height.trans (Credit.elder _ active w.2.1)
  have lpos:0 ≤ ((ll R.draws i).L.val:ℝ):=by positivity
  have paid:=mul_le_mul dated (pow_le_pow_left₀ lpos length a) (pow_nonneg lpos a)
    (zero_le_one.trans (Credit.purchase _ w.1))
  -- Radius will be the size of a genuine test support.
  rw [show (effort G e k u a E W).buy (epoch R t j)=
    (priceWG G e k u a E W).buy (epoch R t j)*(E.buy (epoch R t j))^a by
      unfold effort;rw [Credit.products,Credit.power]]
  have hr:0 ≤ (16*rad)^u:=by positivity
  have pass:=mul_le_mul_of_nonneg_right paid (mul_nonneg hr (pow_nonneg (inv_nonneg.mpr pos.le) a))
  simpa only [div_eq_mul_inv,mul_pow,inv_pow,mul_comm,mul_left_comm,mul_assoc] using pass

def lens (S:Schedule)(m j:ℕ):ℝ:=min 1 (paceT S m j)
lemma journey (R:Realm G (e+1) E)(n m i:ℕ)(gate:R.anchor ≤ n)(route:n ≤ i):
    Escort R n i (lens R.draws.S m):=by
  refine ⟨gate,route,fun j _ _=>le_min zero_le_one (pace_pos ..).le,fun _ _ _=>min_le_left ..,?_⟩
  intro j _ _
  unfold thinLevel lens
  have pos:(1:ℝ)  ≤  (R.draws.S.block j).val:=by exact_mod_cast (R.draws.S.block j).pos
  refine le_min ((div_le_self (le_min zero_le_one (pace_pos ..).le) pos).trans (min_le_left ..)) ?_
  exact (div_le_iff₀ (zero_lt_one.trans_le pos)).mpr ((min_le_right ..).trans_eq (pace_step ..).symm)

theorem earlier (G:Gauge)(k e u:ℕ)(E W:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_room:Dormitory R k u W)(n m i N:ℕ)
      (_gate:R.anchor ≤ n)(_route:n ≤ m)(_edge:m ≤ i)(_stop:i ≤ N)(X:Era G ℝ)(_h:Auth k X)(amount:ℝ),
      Flush e u (paceT R.draws.S m i) X amount →
      let returned:=cruises R.draws R.paid N k i n X
      ∀j ≤ e,∀ω:Fin 0→YForest G, ‖returned.2 j 0 ω‖ ≤ C.buy (epoch R n i)*amount:=by
  obtain ⟨C,carry⟩:=waveSeen G k e u E W
  refine ⟨C,?_⟩
  intro R room n m i N gate route edge stop X h fee paid returned j hj ω
  have regular:Flush e u (lens R.draws.S m i) X fee:=by
    simpa only [lens,min_eq_right (pace_le R.draws.S edge)] using paid
  have ticket:Flush e u (lens R.draws.S m n) returned (C.buy (epoch R n i)*fee):=
    (carry R room n i (lens R.draws.S m) i N N fee (max 0 (R.tempC i i)) (epoch R n i)
      (journey R n m i gate (route.trans edge)) (window R n n i gate le_rfl (route.trans edge)).2.2.2
      le_rfl stop stop (le_max_right _ _) X X (Fringed.same regular h (le_max_left _ _))).f_l
  exact WilsonIndependentMatchedCoverJoined.unit ticket j hj ω

end YM.Integration.WilsonSeparatedPrefixMovingWages
