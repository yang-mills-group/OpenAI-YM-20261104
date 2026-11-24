import YM.Integration.FVA1Physical.Wilson.FluctuationFieldRows
import YM.Integration.FVA1Physical.Wilson.IteratedBankGate

/-! A diffuse incoming polynomial with a rooted subpower credit has subpower
stationary readings after a full normalized interacting block. The reserve is
set before the volume, source and thermal boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film MSbar.Bakery.Portal Next.SectorChange
open scoped Classical Topology BigOperators
variable {G:Gauge}

def packetReserve (p m:ℕ) {η:ℝ} (hη:0<η) : ℝ :=
  min (1/4) (inputSlack p m (bankDegree p m) (half_pos hη)/2)

theorem packetReserve_pos (p m:ℕ) {η:ℝ} (hη:0<η) : 0 < packetReserve p m hη :=
  lt_min (by norm_num) (half_pos (inputSlack_pos ..))

theorem packet_thermal_caps (J:Voice G) (clear:Clear G J) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (simple:G.Simple) (H H':RG.Stage) (P:Patch) (K:KernelChoices) (br:P.Branches K G)
    (p m s:ℕ) (hm:1 ≤ m) {D η:ℝ} (hD:0 ≤ D) (hη:0<η) :
    ∀ᶠ x:ℝ in atTop, ∀ (A:Issue G) (b:Site A.f), A.S.patch=P → A.S.kernel=K →
      Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x;let g:=A.fClock
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      Premier (main A.f A.pre.clip A.pre.path) → Critical A.F A.pre.clip A.pre.path A.ρ → (mold A.pre A.F A.v).PosDef →
      ∀ (Z:Positions (Primary A.c G)) (T:Nesting G A.f), ‖g•Z‖ ≤ D*room y →
      BankPaid b y s p m (packetReserve p m hη) T →
      ∀ i ≤ p,|PowerSeries.coeff i (picture Z (emittedRows A χ (enterRows A T) p))| ≤ y^η := by
  let n:=bankDegree p m
  let d:=n+2*Whisk.ribbon m (p+1+p)+1
  let δ:=packetReserve p m hη
  let ε:=inputSlack p m n (half_pos hη)
  have se:δ < ε:= (min_le_right ..).trans_lt (half_lt_self (inputSlack_pos p m n (half_pos hη)))
  let gy:=Work.E09.betaF_growth G P.L
  have fee: Mosaic.Run atTop (fun x:ℝ=>tip G P.L x) (fun x=>enterFee G s^d*(tip G P.L x)^δ) δ :=
    (Mosaic.Run.core gy δ).mulK gy _
  have fees:=Mosaic.Run.Ypow (tendsto_id (α:=ℝ)) (Mosaic.Run.stanza tendsto_id) (3*(n+1))
  filter_upwards [fluctuation_stationary J clear simple H H' P K br hD,
    fixed_input_rows J clear χ hχ simple H H' P K br p m n s hm (half_pos hη),
    gy.eventually (fees (η/2) (half_pos hη)),(Alto.broad.comp gy).eventually_ge_atTop 2,gy.eventually_gt_atTop 0,
    fee ε se] with x distance fund cash high pos toll
  intro A b hp hk season y g kind profile wedge prem crit pd Z T hz bank i hi
  have a0:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have entry (j:ℕ)(hj:j ≤ p) := enter_vault A s d j a0 {b} T 0 (by rw [Matrix.mulVec_zero];exact bank.through d hj)
  have degree (j:ℕ)(hj:j ≤ p) := (entry j hj).2.trans (bank j hj).1
  have base:=fund A b hp hk season kind profile wedge _ (fun j hj=>⟨Quote.widen (entry j hj).1
    ((le_abs_self _).trans toll) le_rfl,degree j hj⟩) i hi
  have cap:=normalized_input_degree A χ (enterRows A T) p m hm kind pd profile degree hi
  have endpoint:=Bout.across (bulkPoint A (g•Z)) base a0 (by simpa only [sub_zero] using distance A hp hk season (g•Z) hz) cap 0
  have w2:(2:ℝ) ≤ hatW y:=high
  have w1:1+(hatW y)^2 ≤ (hatW y)^3:=by
    nlinarith only [mul_nonneg (sub_nonneg.mpr w2) (sq_nonneg (hatW y)),sq_nonneg (hatW y-1),w2]
  have debit:(1+(hatW y)^2)^(n+1) ≤ y^(η/2) := by
    apply (pow_le_pow_left₀ (by positivity) w1 _).trans
    rw [←pow_mul]
    exact (le_abs_self _).trans cash
  have total := (Bout.looks a0 endpoint).trans (mul_le_mul_of_nonneg_left debit (Real.rpow_nonneg pos.le _))
  rw [←Real.rpow_add pos,add_halves] at total
  have law:=season.case_
  rw [hp] at law
  have gp:0 < g := inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos pos).trans_le law.beta))
  have same:=emitted_read A χ (enterRows A T) p i (by rw [hp,hk];exact br) prem crit pd (g•Z)
  rw [inv_smul_smul₀ gp.ne',normalizedRows_read] at same
  simpa only [picture,PowerSeries.coeff_map,←same] using total

end YM.Integration.FVA1Physical.Wilson
