import YM.Integration.FVA1Physical.Wilson.SourceClockRows
import YM.Integration.FVA1Physical.Wilson.SceneResetRate

/-! Apply the change of coordinates to the coupling action of the very same
realized RG step. Its price is subpower uniformly in the number of sites,
fields and periods, for every fixed jet order and degree. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Tree Precision
open MSbar MSbar.Cacao MSbar.Bakery MSbar.Wave MSbar.Rolling.Price MSbar.Whisk MSbar.Rolling MSbar.Bakery.Portal
open MSbar.Mosaic MSbar.Midpoint MSbar.Lis PhysicalNext.Repeat.Legato Push Push.Uniform
open scoped Classical Topology BigOperators
variable {σ ι:Type} [Fintype σ] [DecidableEq σ] {G:Gauge}

theorem clock_fee_subpower (p m e:ℕ) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ x:ℝ in atTop, sourceClockFee p m (hatW x^e) ≤ x^ε := by
  let h:=Alto.jewel p e m p
  have large:Alto.Tuition (fun t:ℝ=>sourceClockFee p m (t^e)) h := by
    apply Alto.Tuition.items
    intro j hj
    apply Alto.Tuition.items
    intro d hd
    apply (Alto.termB p e d j).strong
    change e*d+p*e*j ≤ e*m+p*e*p
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp (mem_range.mp hd)))
      (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp (mem_range.mp hj)))
  have height:=Alto.Tuition.down large (Nat.lt_succ_self h)
  have rise:Tendsto (fun x:ℝ=>x) atTop atTop:=tendsto_id
  have reserve:=Mosaic.Run.Ypow rise (Mosaic.Run.stanza rise) (h+1)
  filter_upwards [(height.comp Alto.broad).eventually (ge_mem_nhds zero_lt_one),
    Alto.broad.eventually_gt_atTop 0,reserve ε hε] with x small pos cash
  calc sourceClockFee p m (hatW x^e) ≤ (hatW x)^(h+1) := (div_le_one (pow_pos pos _)).mp small
       _ ≤ |(hatW x)^(h+1)| := le_abs_self _
       _ ≤ x^ε := cash

theorem clock_vault_subpower (s h p m:ℕ) {ε:ℝ} (hε:0<ε) : ∀ᶠ y:ℝ in atTop,
    ∀ (τ:Type) [Fintype τ] [DecidableEq τ] (c:Side) (l:τ→Site c) (W:Finset (Site c))
      (b:PowerSeries ℝ) (T:PowerSeries (Pot τ)) (a:ℝ),
      PowerSeries.coeff 0 b=1 → (∀ j ≤ p, |PowerSeries.coeff j b| ≤ Alto.purse Alto.Dean (hatW y) j) →
      (∀ j ≤ p,Vault l W a s h 0 (PowerSeries.coeff j T) (y^(ε/2))) →
      ∀ i ≤ p, Vault l W a s h 0 (PowerSeries.coeff i (sourceClock m b T)) (y^ε) := by
  filter_upwards [clock_fee_subpower p m (Alto.Dean p) (half_pos hε),Alto.broad.eventually_ge_atTop 1,
    eventually_gt_atTop (0:ℝ)] with y bill wide pos
  intro τ _ _ c l W b T a unit cost input i hi
  let D:=(hatW y)^(Alto.Dean p)
  have paid:Bronze.brim p b D:=fun j hj=>(cost j hj).trans (pow_le_pow_right₀ wide (Alto.ranked hj))
  have ok:=sourceClock_vault l W s h p m T b unit paid (one_le_pow₀ wide) input i hi
  apply Quote.widen ok.1 _ le_rfl
  calc sourceClockFee p m D*y^(ε/2) ≤ y^(ε/2)*y^(ε/2) :=
         mul_le_mul_of_nonneg_right bill (Real.rpow_nonneg pos.le _)
       _ = y^ε := by rw [← Real.rpow_add pos]; congr 1; ring

omit [DecidableEq σ] in
/-- The scaled coarse field and the coupling `tiltMap` used to build the
physical scene are precisely those used in the source conversion. -/
theorem realized_source_clock (R:PhysicalNext.Repeat.Legato.Run G) {N n k j p:ℕ} {e:G.Color}
    (S:Scene R.family.path.levels n p) (realized:Realized (RunFormalChain.fromRun R).kin N n k p e S)
    (kj:k ≤ j) (jN:j<N) (m:ℕ) (T:PowerSeries (Pot σ)) (deg:∀ i ≤ p, (PowerSeries.coeff i T).totalDegree ≤ m)
    {K:ℝ→ι→Prop} (x:ℝ→ι→View σ) (hx:Price K 0 x) :
    Price K (p+1) (fun g i=>taste p (picture (taste p (S.action j) g • x g i) T) (tiltMap (S.action j) p g) -
      taste p (picture (x g i) (sourceClock m (S.action j) T)) g) := by
  obtain ⟨_,_,unit,_,_⟩:=realized.step j jN kj
  exact sourceClock_price p m T deg x hx unit (manifest p _)

end YM.Integration.FVA1Physical.Wilson
