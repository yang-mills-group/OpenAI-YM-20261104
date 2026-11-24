import YM.Integration.WilsonIndependentMovingRosterAllFineAge

/-! The chronological credit at fixed physical radii is uniform in the
auxiliary cutoff. Only the two measured scale ratios and the own-date
price of the older receiver enter. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterAllFineClock
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E:Credit}

private theorem salary (C:Credit)(a η:ℝ)(gain:0 < η):
    ∀ᶠ x:ℝ in atTop,∀w:ℝ,0 ≤ w → w ≤ a*x → C.buy w ≤ Real.exp (η*x):=by
  have slow:Tendsto (fun x:ℝ=>x^C.d*Real.exp (-(η*x))) atTop (𝓝 0):=by
    simpa only [Real.rpow_natCast,neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C.d:ℝ) η gain
  have vanish:Tendsto (fun x:ℝ=>C.x*a^C.d*(x^C.d*Real.exp (-(η*x)))) atTop (𝓝 0):=by
    simpa only [mul_zero] using slow.const_mul (C.x*a^C.d)
  filter_upwards [vanish.eventually_le_const zero_lt_one] with x paid w nn bound
  have prev:C.buy w*Real.exp (-(η*x)) ≤ 1:=calc
    _ ≤ C.x*(a*x)^C.d*Real.exp (-(η*x)):=by
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nn bound _) (zero_le_one.trans C.good)) (Real.exp_pos _).le
    _=C.x*a^C.d*(x^C.d*Real.exp (-(η*x))):=by rw [mul_pow];ring
    _ ≤ 1:=paid
  have earned:=mul_le_mul_of_nonneg_right prev (Real.exp_pos (η*x)).le
  rwa [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at earned

/-- The opening is chosen before any board, top or cutoff. The last scale
ratio is charged to the actual stop below the exterior. -/
theorem original (C:Credit)(B P Q η:ℝ)(gain:0 < η):
    ∃opening:ℝ,∀g:ℝ,0 < g → opening ≤ -Real.log g →
    ∀(R:Realm G e E)(older t m:ℕ),R.anchor ≤ older → older ≤ t → t ≤ m → R.y older ≤ B →
      Real.log (paceT R.draws.S m t) ≤ P*(-Real.log g) →
      Real.log (paceT R.draws.S t older) ≤ Q*(-Real.log g) →
      C.buy (epoch R older m) ≤ g^(-η):=by
  let a:=max 1 (1+2*(P+Q))
  have ready:=salary C a η gain
  obtain ⟨x₀,threshold⟩:=eventually_atTop.1 ready
  refine ⟨max 1 (max x₀ B),?_⟩
  intro g positive opened R older t m live before after prior ruler beyond
  let x:ℝ:= -Real.log g
  have pos:1 ≤ x:=(le_max_left ..).trans opened
  have lo:x₀ ≤ x:=(le_max_left x₀ B).trans ((le_max_right ..).trans opened)
  have age:R.y older ≤ x:=prior.trans ((le_max_right ..).trans ((le_max_right ..).trans opened))
  have room:(1+2*(P+Q))*x ≤ a*x:=mul_le_mul_of_nonneg_right (le_max_right ..) (zero_le_one.trans pos)
  have limit:=threshold x lo (epoch R older m)
    (zero_le_one.trans (window R older older m live le_rfl (before.trans after)).1)
  have band:epoch R older m ≤ a*x:=by
    rw [WilsonIndependentMovingRosterAllFineAge.rulers R older t m]
    change Real.log (paceT R.draws.S m t) ≤ P*x at ruler
    change Real.log (paceT R.draws.S t older) ≤ Q*x at beyond
    linarith only [age,ruler,beyond,room,show (1+2*(P+Q))*x=x+2*(P*x+Q*x) by ring]
  rw [Real.rpow_def_of_pos positive]
  exact (limit band).trans_eq (by dsimp only [x];congr 1;ring)

/-- A polynomial position/capture wallet in the same physical logarithm
can pay any fixed-order shape cost without dependence on the inversion mesh. -/
theorem shapes (C shape:Credit)(η:ℝ)(gain:0 < η):
    ∃opening:ℝ,∀g:ℝ,0 < g → opening ≤ -Real.log g →
    ∀r:ℝ,1 ≤ r → r ≤ shape.buy (-Real.log g) → C.buy r ≤ g^(-η):=by
  obtain ⟨x₀,earned⟩:=eventually_atTop.1 (salary (C.usingC shape) 1 η gain)
  refine ⟨max 1 x₀,?_⟩
  intro g pos cost r one reach
  let x:= -Real.log g
  have low:1 ≤ x:=(le_max_left ..).trans cost
  have enough:x₀ ≤ x:=(le_max_right ..).trans cost
  have paid:=earned x enough x (zero_le_one.trans low) (by simp)
  rw [Credit.stock_up] at paid
  rw [Real.rpow_def_of_pos pos]
  exact ((C.elder one reach).trans paid).trans_eq (by dsimp only [x];congr 1;ring)

end YM.Integration.WilsonIndependentMovingRosterAllFineClock

