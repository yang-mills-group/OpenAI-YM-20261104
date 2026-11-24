import YM.Integration.FVA1Physical.Wilson.CoarseLand

/-! Purchase the coarse spatial weight and the derivative costs of the
stationary substitution using the tabulated prices of this very Run. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG YM.Wilson Precision MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Mosaic
open scoped Classical Topology
variable {G:Gauge}

theorem rail_sale (simple:G.Simple) (M:MapPrices) (P:Patch) (s q:ℕ) {δ:ℝ} (hd:0<δ) :
    ∀ᶠ x:ℝ in atTop, let y:=tip G P.L x
      0 ≤ αm y ∧ αm y ≤ railWidth M P ∧ αm x ≤ αm y*P.L.val ∧
        ∀ k≤q, railFee G M P s ^k * y^δ ≤ x^(2*δ) := by
  have rate:0<railWidth M P:=by unfold railWidth; exact div_pos (div_pos (M.alpha_pos _) (by positivity)) (by norm_num)
  have gy:=Work.E09.betaF_growth G P.L
  have decay:=(Geneva.ray gy).eventually (ge_mem_nhds rate)
  have hx':=(Mosaic.Run.shift (X:=fun x:ℝ=>x) tendsto_id tendsto_id G simple P.L δ).2
  have cash:1 ≤ railFee G M P s:=le_max_left ..
  filter_upwards [decay,Alto.drift_scale simple P.L, hx'.eventually (ge_mem_nhds one_lt_two),
    (tendsto_rpow_atTop hd).eventually_ge_atTop (2*railFee G M P s^q),eventually_gt_atTop (0:ℝ),
    gy.eventually_gt_atTop 0] with x decay drift ratio enough hx hy y
  let u:=Alto.flurry x
  let v:=Alto.flurry y
  have u0:0<u:=zero_lt_one.trans_le drift.1
  have v0:0<v:=u0.trans_le drift.2.1
  have power:v^3 ≤ u^3*(P.L.val:ℝ) :=by
    refine (pow_le_pow_left₀ v0.le drift.2.2 3).trans ?_
    rw [mul_pow,mul_comm (u^3)]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg u0.le 3)
    have hc:3≤(P.L.val:ℝ):=by exact_mod_cast P.coarse
    norm_num
    linarith
  have rebalance : (u^3)⁻¹ /(P.L.val:ℝ) ≤ (v^3)⁻¹ := by
    apply le_trans (le_of_eq _) (inv_anti₀ (pow_pos v0 _) power)
    rw [mul_inv,div_eq_mul_inv]
  refine ⟨show 0≤v^(-3:ℤ) from zpow_nonneg v0.le _,decay,?_,?_⟩
  · unfold αm
    simp only [_root_.zpow_neg]
    exact (div_le_iff₀ (show 0<(P.L.val:ℝ) from by positivity)).mp rebalance
  intro k hk
  have ybill:y^δ ≤ 2*x^δ :=(div_le_iff₀ (Real.rpow_pos_of_pos hx δ)).mp ratio
  calc
    railFee G M P s^k*y^δ ≤ railFee G M P s^q*(2*x^δ) :=
      mul_le_mul (pow_le_pow_right₀ cash hk) ybill (Real.rpow_nonneg hy.le _) (pow_nonneg (zero_le_one.trans cash) _)
    _ = (2*railFee G M P s^q)*x^δ := by ring
    _ ≤ x^δ*x^δ := mul_le_mul_of_nonneg_right enough (Real.rpow_nonneg hx.le _)
    _ = x^(2*δ) :=by rw [←Real.rpow_add hx];congr 1;ring

def railMenu (simple:G.Simple) (M:MapPrices) (H _H':Stage) (P:Patch) (_K:KernelChoices) : ℝ :=
  ∑ t:Fin (H.order+1) × Fin (H.order+1),
    |(eventually_atTop.mp (rail_sale simple M P t.1.val H.order (margin_pos t.2.val))).choose|

theorem railMenu_covers (simple:G.Simple) (M:MapPrices) (H H':Stage) (P:Patch) (K:KernelChoices)
    {s h:ℕ} (hs:s≤H.order) (hh:h≤H.order) {x:ℝ} (grant:railMenu simple M H H' P K≤x) :
    let y:=tip G P.L x
    0≤αm y ∧ αm y≤railWidth M P ∧ αm x≤αm y*P.L.val ∧
      ∀ k≤H.order,railFee G M P s^k*y^(margin h)≤x^(2*margin h) := by
  let t:Fin (H.order+1) × Fin (H.order+1):=(⟨s,by omega⟩,⟨h,by omega⟩)
  let fees (e:Fin (H.order+1) × Fin (H.order+1)):=
    (eventually_atTop.mp (rail_sale simple M P e.1.val H.order (margin_pos e.2.val))).choose
  have cut:fees t≤x:=(le_abs_self _).trans ((single_le_sum (fun j _=>abs_nonneg (fees j)) (mem_univ t)).trans grant)
  exact (eventually_atTop.mp (rail_sale simple M P s H.order (margin_pos h))).choose_spec x cut

end YM.Integration.FVA1Physical.Wilson
