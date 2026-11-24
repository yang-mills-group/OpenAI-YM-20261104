import YM.Integration.WilsonPhysicalLocalPlaquetteReserve
import YM.Next.RANK.Determinant
import YM.RG16.Unmasked.Pace

/-! Area, no wrap and face census before every period, on the original paced
Wilson schedule. The side bound uses its actual finer block factor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestArea
open Filter Lattice Wilson RG OPE.Therm RG16
open WilsonPhysicalLocalPlaquetteForest WilsonPhysicalLocalPlaquetteReserve
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem wraps (C : Family G) (H:ℕ) :
    ∀ᶠ m:ℕ in atTop,∀p D,D≤H → 2*radius D (C.path.levels.clock.op m p).ratio.count.val<(C.side (m+1) p).val := by
  let S:=C.path.levels.S
  filter_upwards [S.den_strict.tendsto_atTop.eventually_ge_atTop (2*H+12)] with m old p D hd
  let L:=(S.block m).val
  have l : 0<L:=(S.block m).property
  change 2*(D+4*L+1)<(S.period p).val*((S.denominator m).val*L)
  have reach:2*H≤2*H*L:=Nat.le_mul_of_pos_right _ l
  apply Nat.lt_of_lt_of_le _ ((Nat.mul_le_mul_right L old).trans (Nat.le_mul_of_pos_left _ (S.period p).property))
  nlinarith only [reach,l,hd]

/-- The slow price is precisely the block clause of the retained original
Wilson reporting appointment. The finite support cap is chosen before dates. -/
theorem dates (C : Family G) (simple:G.Simple)
    (slow:∀m,((C.path.levels.S.block m).val:ℝ)≤Real.log (Lambda C.path.levels m))
    (H:ℕ) {ε:ℝ} (pos:0<ε) : ∀ᶠ m:ℕ in atTop,∀p D,D≤H→
    let A:=C.path.levels
    let L:=(A.clock.op m p).ratio.count.val
    2*radius D L<(C.side (m+1) p).val ∧ area D L*cool A (m+1)≤ε ∧
      ∀o:Site (C.side (m+1) p),((WilsonAxialWindow.cells o (radius D L)).card:ℝ)≤A.clock.hatBeta (m+1) := by
  let A:=C.path.levels
  let X:ℝ:=(tariff H+1)^4*Fintype.card PlaqAxes
  have grows:=(Next.Rank.Station.hat_rate A simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [wraps C H,(Real.tendsto_log_atTop.comp grows).eventually_ge_atTop (1:ℝ),
    grows.eventually (small (tariff H) 20 pos),grows.eventually (small X 16 zero_lt_one)] with m winding hs areaFee countFee p D hd
  let L:=(A.clock.op m p).ratio.count.val
  let b:=A.clock.hatBeta (m+1)
  let s:=Real.log b
  change 1 ≤ s at hs
  change tariff H*s^20*(Real.sqrt b)⁻¹≤ε at areaFee
  change X*s^16*(Real.sqrt b)⁻¹≤1 at countFee
  have b1:1<b:=A.fits.delayed _
  have sq:0<Real.sqrt b:=Real.sqrt_pos.mpr (zero_lt_one.trans b1)
  have s4 : 1 ≤ s ^ 4:=one_le_pow₀ hs
  have lbound:(L:ℝ)≤2+s:=(slow m).trans ((Real.log_le_self (Literal.lambda_pos C m).le).trans
    ((Literal.lambda_mono C simple).monotone (Nat.le_succ m)))
  have d0:0≤(H:ℝ):=H.cast_nonneg
  have d1:(D:ℝ)≤H:=by exact_mod_cast hd
  have h4 : (H:ℝ)≤H*s^4:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left s4 d0
  have room:=scalar H D L hs (by linarith only [d1,d0,h4]) (by linarith only [hs,lbound])
  refine ⟨winding p D hd,?_,?_⟩
  · change area D L*((Real.sqrt b)⁻¹*s^12)≤ε
    calc
      _=(area D L*s^12)*(Real.sqrt b)⁻¹:=by ring
      _≤(tariff H*s^20)*(Real.sqrt b)⁻¹:=mul_le_mul_of_nonneg_right room.2 (inv_nonneg.mpr sq.le)
      _≤ε:=areaFee
  · intro o
    let r:=radius D L
    have span:(r:ℝ)+r+1≤(tariff H+1)*s^4:=by dsimp [r];linarith only [room.1,s4]
    have cap:((WilsonAxialWindow.cells o r).card:ℝ)≤((r:ℝ)+r+1)^4*Fintype.card PlaqAxes:=by exact_mod_cast WilsonAxialWindow.count o r
    have spend:X*s^16≤Real.sqrt b:=(div_le_one₀ sq).mp (by rw [div_eq_mul_inv];exact countFee)
    calc
      _≤((r:ℝ)+r+1)^4*Fintype.card PlaqAxes:=cap
      _≤((tariff H+1)*s^4)^4*Fintype.card PlaqAxes:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) span 4) (by positivity)
      _=X*s^16:=by dsimp [X];ring
      _≤Real.sqrt b:=spend
      _≤b:=by nlinarith only [Real.sq_sqrt (zero_lt_one.trans b1).le,Real.one_le_sqrt.mpr b1.le]

end YM.Integration.WilsonReportingForestArea
