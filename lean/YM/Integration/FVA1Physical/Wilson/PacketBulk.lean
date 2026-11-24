import YM.Integration.FVA1Physical.Wilson.FluctuationColumns
import YM.Integration.FVA1Physical.Wilson.IteratedBankGate
import YM.Integration.FVA1Physical.Sources.Round2.PosteriorReclock
import YM.Integration.FVA1Physical.Round2.StencilExteriorTests

/-! The actual inherited packet, after the normalized local Gaussian step, has
the independently generated stationary Wilson coefficients. The estimate is
uniform over all tori and all rooted distributed polynomials in their original norm. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Wave
open MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.Midpoint MSbar.Bakery
open MSbar.Bakery.Portal MSbar.Bakery.Film MSbar.Tramp Push.Uniform Next.SectorChange
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem BankPaid.weaken_weight {f:Side} {b:Site f} {y δ:ℝ} {s t m p:ℕ} {T:Nesting G f}
    (bank:BankPaid b y s p m δ T) (ht:t ≤ s) : BankPaid b y t p m δ T := by
  intro i hi
  obtain ⟨deg,v⟩:=bank i hi
  refine ⟨deg,v.1,fun k hk=>(shiny (ι:=Primary f G) k ?_).trans (v.2 k hk)⟩
  intro w _
  unfold Whisk.rate Whisk.spread liftW
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)) ht) (Real.exp_pos _).le

theorem packet_bulk (χ:ChartRatio G) (charts:LocalRatio χ) (V:Voice G) (clear:Clear G V)
    (simple:G.Simple) (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G)
    (p s degree q:ℕ) {D δ:ℝ} (hD:0 ≤ D) (hδ:δ<1) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Mosaic.Issue G) (Z:Positions (Primary A.c G)) (b:Site A.f) (T:Nesting G A.f),
      A.S.patch=P → A.S.kernel=K → Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x;let g:=A.fClock
      ‖g • Z‖ ≤ D*room y → Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      Premier (main A.f A.pre.clip A.pre.path) → Critical A.F A.pre.clip A.pre.path A.ρ →
      (mold A.pre A.F A.v).PosDef → BankPaid b y s p degree δ T →
      ∀ (pal:Palisade) (U:Config G A.f), U∈A.regionX y b Z V pal →
      |taste p (innerColumn A χ V y (g•Z) b U (enterRows A T) p) g -
        clockReading p g (emittedRows A χ (enterRows A T) p) Z| ≤ (p+1:ℕ)*y^(-(q:ℝ)) := by
  let m:=max degree (p+2)
  have grow:=Work.E09.betaF_growth G P.L
  have fee: Mosaic.Run atTop (fun x:ℝ=>tip G P.L x) (fun x=>enterFee G s^m*(tip G P.L x)^δ) δ :=
    (Mosaic.Run.core grow δ).mulK grow _
  filter_upwards [fluctuation_columns V clear χ charts simple H H' P K branch p s m q (le_max_right ..) hD,
    fee 1 hδ,grow.eventually_ge_atTop 2] with x paid toll high
  intro A Z b T patch kernel season y g hz kind plane wedge prem crit pd bank pal U inside
  have law:=season.case_
  rw [patch] at law
  have β:1 ≤ A.pre.beta:=by linarith only [law.beta,high]
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le β))
  have cap:g ≤ 1:=inv_le_one_of_one_le₀ (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt β)
  have ha:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have maxpay:enterFee G s^m*y^δ ≤ y:=(le_abs_self _).trans (by simpa only [Real.rpow_one] using toll)
  have rows:=paid A (g•Z) b patch kernel season hz kind plane wedge (enterRows A T) (fun i hi=>by
    have v:=bank.through m hi
    have entry:=enter_vault A s m i ha {b} T 0 (by rw [Matrix.mulVec_zero];exact v)
    exact ⟨Quote.widen entry.1 maxpay le_rfl,entry.2.trans ((bank i hi).1.trans (le_max_left ..))⟩) U inside
  have matchJ:∀ i ≤ p,PowerSeries.coeff i (bulkColumn A χ (g•Z) (enterRows A T) p)=
      PowerSeries.coeff i (picture Z (emittedRows A χ (enterRows A T) p)) := by
    intro i _
    rw [emitted_read A χ (enterRows A T) p i (by rw [patch,kernel];exact branch) prem crit pd,
      inv_smul_smul₀ gp.ne',picture,PowerSeries.coeff_map]
  apply finite_taste_transfer p _ _ gp.le cap
  intro i hi
  rw [←matchJ i hi,abs_sub_comm]
  exact rows i hi

end YM.Integration.FVA1Physical.Wilson
