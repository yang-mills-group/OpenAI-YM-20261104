import YM.Integration.WilsonRegisteredAxialRates
import YM.Integration.WilsonRegisteredWholeShort

/-! The actual positive angular threshold on a moving nonwrapping
box buys the complete previously registered projected regular column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialChart
open Filter Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonRegisteredAffineHalo WilsonRegisteredWidthCurrency WilsonReportingForestAngularReflection
open WilsonRegisteredAxialRates WilsonInheritedRegisteredField WilsonReportingForestAngularFare
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem fit (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (p base:ℕ):
    ∀ᶠ m:ℕ in atTop,∀ N per (_live:m+1 ≤ N),
      let k:=m+1
      let H:=radius R p (base+1) k
      let r:=amplitude R J H N per k
      let τ:=angularCut (β k)
      let c:=(4*(H:ℝ)*Fintype.card PlaqAxes)*τ
      let θ:=(R.family.path.rep N per k).p.threshold
      0<r ∧ 0 ≤ τ ∧ c ≤ J.δ ∧ J.C*c ≤ r*θ ∧ r*θ ≤ J.r ∧ 4*J.C*r ≤ 1:=by
  let ε:=min (min J.δ J.r) (4*J.C)⁻¹
  have jp:0<J.C:=zero_lt_one.trans_le clear.cost
  have ep:0<ε:=lt_min (lt_min clear.dist clear.depth) (by positivity)
  have logs:=(Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (A) simple)).eventually_ge_atTop 1
  filter_upwards [paid R simple slow J clear p (base+1) 0 ep,
    (tendsto_add_atTop_nat 1).eventually logs] with m pay late
  intro N per live k H r τ c θ
  let s:=Real.log (β k)
  let gh:=(A).clock.hatCoupling k
  let g:=Pert.Asymptotics.regulatorRun R.family N per k
  have sp:1 ≤ s:=late
  have s0:0<s:=zero_lt_one.trans_le sp
  have gp:0<gh:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans ((A).fits.delayed k)))
  have gc:gh ≤ 2*g:=(IterationFour.Currency.hat_g R.makes N per k live).1
  have positive:0<g:=by linarith only [gc,gp]
  have first:Real.sqrt s ≤ s:=by nlinarith only [Real.sq_sqrt s0.le,Real.sqrt_nonneg s,sp,sq_nonneg (Real.sqrt s-1)]
  have next:1 ≤ Real.sqrt s:=by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt sp
  have second:Real.sqrt (Real.sqrt s) ≤ Real.sqrt s:=by
    nlinarith only [Real.sq_sqrt (Real.sqrt_nonneg s),Real.sqrt_nonneg (Real.sqrt (Real.sqrt s)),next,sq_nonneg (Real.sqrt (Real.sqrt s)-1)]
  have limit:τ ≤ gh*s^2:=(mul_le_mul_of_nonneg_left (second.trans first) (mul_nonneg gp.le s0.le)).trans_eq (by ring)
  have t0:0 ≤ τ:=by change 0 ≤ gh*s*Real.sqrt (Real.sqrt s);positivity
  have theta:0<θ:=(R.family.path.rep N per k).p.threshold_pos
  have wEq:WilsonRegisteredAffineSource.width R N per k=(g*(s^2/32))/θ:=rfl
  have hp:0<(H:ℝ):=by
    have h:0<H:=by dsimp only [H,radius];omega
    exact_mod_cast h
  have wp:0<WilsonRegisteredAffineSource.width R N per k:=by rw [wEq];positivity
  have rp:0<r:=by dsimp only [r,amplitude];positivity
  have invoiced:r ≤ ε:=by simpa only [pow_zero,mul_one] using (pay N per live).2
  have settled:J.C*c ≤ r*θ:=by
    calc
      _ ≤ J.C*((4*(H:ℝ)*Fintype.card PlaqAxes)*((2*g)*s^2)):=by
        dsimp only [c]
        gcongr
        exact limit.trans (mul_le_mul_of_nonneg_right gc (sq_nonneg s))
      _=r*θ:=by dsimp only [r,amplitude];rw [wEq];field_simp;ring
  have relaxed:r*θ ≤ r:=mul_le_of_le_one_right rp.le (R.family.path.rep N per k).p.threshold_le
  have c0:0 ≤ c:=by dsimp only [c];positivity
  refine ⟨rp,t0,(le_mul_of_one_le_left c0 clear.cost).trans (settled.trans (relaxed.trans (invoiced.trans ((min_le_left ..).trans (min_le_left ..))))),
    settled,relaxed.trans (invoiced.trans ((min_le_left ..).trans (min_le_right ..))),?_⟩
  calc 4*J.C*r ≤ (4*J.C)*(4*J.C)⁻¹:=mul_le_mul_of_nonneg_left (invoiced.trans (min_le_right ..)) (by positivity)
       _=1:=mul_inv_cancel₀ (by positivity)

theorem measured (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (p base t:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m+1 ≤ N) d (_ref:R.family.ref d ≤ m+1)
      (v:R.family.label d) (o:Site (R.family.side (m+1) per)),
      let k:=m+1
      let b:=WilsonDegreeFourInheritedRange.height R p k
      let H:=radius R p (base+1) k
      let P:=R.family.path.rep N per k
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      10*H<(R.family.side k per).val → ∀ U∈House.chilly (WilsonAxialWindow.cells o H) (angularCut (β k)),
      ‖∑' i,if coverNumber P.p.B (Z.support i)<b then Z.maskedTerm P i U else 0‖*(Real.log (β k))^t
        ≤ ε*L.coeffSize (L.core Z.x):=by
  filter_upwards [fit R simple slow J clear p base,paid R simple slow J clear p (base+1) t he] with m funds rates
  intro N per live d ref v o k b H P Z L period U cold
  let r:=amplitude R J H N per k
  have shape:P.p=(A).budget k:=(R.makes.wilson.represents N per k live).vac
  have place:b*(4*P.p.B+2)+2*P.p.B<H:=by
    rw [shape];change b*(4*(A).clock.coverSize k+2)+2*(A).clock.coverSize k<base+1+b*(4*(A).clock.coverSize k+2)+2*(A).clock.coverSize k
    omega
  obtain ⟨rp,weak,cost,cash,cap,stay⟩:=funds N per live
  have sale:=WilsonRegisteredWholeShort.field R J clear a live ref v o b H _ r weak rp U cold place period cost cash cap stay
  have price:=(rates N per live).1
  have s0:0 ≤ Real.log (β k):=Real.log_nonneg ((A).fits.delayed k).le
  calc
    _ ≤ (r*(((A).params k).columns*L.coeffSize (L.core Z.x)))*(Real.log (β k))^t:=
      mul_le_mul_of_nonneg_right sale (pow_nonneg s0 t)
    _=(r*((A).params k).columns*(Real.log (β k))^t)*L.coeffSize (L.core Z.x):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_right price (Finset.sum_nonneg fun _ _=>norm_nonneg _)

end YM.Integration.WilsonRegisteredAxialChart
end
