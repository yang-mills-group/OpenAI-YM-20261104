import YM.Integration.FVA1Physical.Wilson.FluctuationStationary
import YM.Integration.FVA1Physical.Wilson.BankDegree
import YM.Integration.FVA1Physical.Wilson.UniformInputSlack

/-! Every rooted derivative row of the normalized mixed field coefficient,
on the full fluctuation-scale family of independently tested retained fields. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {κ:Type} [Fintype κ]

theorem fluctuation_field_rows (I:κ→Lamp G) (J:Voice G) (clear:Clear G J) (χ:ChartRatio G)
    (hχ:LocalRatio χ) (simple:G.Simple) (H H':RG.Stage) (P:Patch) (K:KernelChoices) (br:P.Branches K G)
    (p s h L:ℕ) (part:Bool) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) :
    ∀ᶠ x:ℝ in atTop, ∀ (A:Issue G) (b:Site A.f), A.S.patch=P → A.S.kernel=K →
      Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ (z:Positions (Primary A.c G)), ‖z‖ ≤ D*room y → ∀ o:κ→Site A.f,
      (∀ t:Slice I,separation b (legs I o t).1 ≤ L*closeN y) → ∀ i ≤ p,
        Vault (address A.F G) {b} (αm y) s h (bulkPoint A z)
          (PowerSeries.coeff i (normalizedRows A χ (jointFieldBank I A o part) p)) (y^η) := by
  let m:=p+1
  let n:=m*(p+1+p)+2
  let gy:=Work.E09.betaF_growth G P.L
  obtain ⟨v,buy⟩:=purchased_fluctuation_chance J clear simple H H' P K br hD 0
  obtain ⟨_,_,theater⟩:=waiting v H H' J χ hχ clear P 3 0
  have rise:Tendsto (fun y:ℝ=>y) atTop atTop:=tendsto_id
  have fees:=Mosaic.Run.Ypow rise (Mosaic.Run.stanza rise) (3*(n+1))
  filter_upwards [fluctuation_stationary J clear simple H H' P K br hD,buy,theater,
    fixed_input_rows J clear χ hχ simple H H' P K br p m n s (by dsimp only [m];omega) (half_pos hη),
    gy.eventually (field_vault_subpower I p s (n+2*Whisk.ribbon m (p+1+p)+1) L part
      (inputSlack_pos p m n (half_pos hη))), gy.eventually (fees (η/2) (half_pos hη)),
    (Alto.broad.comp gy).eventually_ge_atTop 2,gy.eventually_gt_atTop 0]
    with x distance select hall fund source cash high pos
  intro A b hp hk season y kind profile wedge z hz o near i hi
  let src:=jointFieldBank I A o part
  obtain ⟨grants,cal,_,_⟩:=select A hp hk season z b hz
  have suite:=(hall.enter _ _ hp season (boxX y b) (boxY y b) A.F z A.v grants
    (by rw [hp];exact cal.first)).2
  have bank:=source A o b near
  have degree (t:ℕ)(ht:t ≤ p):(PowerSeries.coeff t src).totalDegree ≤ m:=
    (bank t ht).2.trans (by dsimp only [m];omega)
  have base:=fund A b hp hk season kind profile wedge src (fun t ht=>⟨(bank t ht).1,degree t ht⟩) i hi
  have cap:=normalized_input_degree A χ src p m (by dsimp only [m];omega) kind suite.positivity profile degree hi
  have a0:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have endpoint:=Bout.across (bulkPoint A z) base a0 (by simpa only [sub_zero] using distance A hp hk season z hz) cap h
  have w2:(2:ℝ) ≤ hatW y:=high
  have w1:1+(hatW y)^2 ≤ (hatW y)^3:=by
    nlinarith only [mul_nonneg (sub_nonneg.mpr w2) (sq_nonneg (hatW y)),sq_nonneg (hatW y-1),w2]
  have debit:(1+(hatW y)^2)^(n+1) ≤ y^(η/2) := by
    apply (pow_le_pow_left₀ (by positivity) w1 _).trans
    rw [←pow_mul]
    exact (le_abs_self _).trans cash
  apply Quote.widen endpoint _ le_rfl
  calc y^(η/2)*(1+(hatW y)^2)^(n+1) ≤ y^(η/2)*y^(η/2) :=
         mul_le_mul_of_nonneg_left debit (Real.rpow_nonneg pos.le _)
       _ = y^η := by rw [←Real.rpow_add pos];congr 1;ring

end YM.Integration.FVA1Physical.Wilson
