import YM.Integration.WilsonPhysicalHistoryRetainedSpringJointPrice

/-! A correlated spectator changes the moment order, while the number of
previous vertices still determines how their total exponent loss is shared. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Finset Lattice RG Wilson WilsonStartup Pert.Asymptotics Pressure
open ConnectedActivityE6 PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic RGLocalTaylor
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem cofinal_joint_load (R : Run G) (simple : G.Simple) (credit : Credit) (d K n l : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N per : ℕ,m<N →
      let S:=V.clock.op m per
      let g:=regulatorRun R.family N per (m+1)
      let D:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∀ {W : ℝ} (σ : Fin (n+1)→ℝ), (∀ j,0<σ j) → (∀ j,(σ j)⁻¹≤zz V (m+1)) →
      ∀ o : Target.Order G W,
      WilsonCoherentMayerCovarianceCalendar.deviation G S.patch.L o≤1+Real.log (betaF G (V.clock.hatBeta m) S.patch.L) →
      ∀ a : Fin (n+1)→PrismA G,(∀ j,(a j).grade≤d) → 0≤D →
      let cost:=fun j r=>occurrencePrice G S.patch.L o.eta o.gap o.ample (σ j) D (a j) r (l+1)
      (∏ j,max (cost j (a j).rise) (cost j ((a j).rise+K)))≤ε*g^(-η) := by
  intro V
  let u:=min 1 ε
  have u0 : 0<u:=lt_min zero_lt_one ep
  have h : 0<η/(n+1:ℕ):=by positivity
  filter_upwards [cofinal_moment_price R simple credit d 0 l u0 h,
    cofinal_moment_price R simple credit d K l u0 h] with m base extra
  intro N per later S g D W σ width scope o paid a cap d0 cost
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per (m+1) later
  have nonneg (j : Fin (n+1)) : 0≤cost j (a j).rise:=by
    dsimp only [cost,occurrencePrice]
    have M:=(speed_price_pos G S.patch.L o.eta o.gap o.ample (((a j).rise+2)*(l+1)-1)).le
    positivity [width j]
  have one (j : Fin (n+1)) :
      max (cost j (a j).rise) (cost j ((a j).rise+K))≤u*g^(-(η/(n+1:ℕ))):=by
    apply max_le
    · simpa only [cost,occurrencePrice,Nat.add_zero,D,S,V,g] using
        base N per later (width j) (scope j) o paid (a j) (cap j)
    · exact extra N per later (width j) (scope j) o paid (a j) (cap j)
  have exponent : (g^(-(η/(n+1:ℕ))))^(n+1)=g^(-η):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul gp.le]
    congr 1
    have count : ((n+1:ℕ):ℝ)≠0:=by positivity
    field_simp
  have weight : u^(n+1)≤ε:=by
    rw [pow_succ]
    exact (mul_le_of_le_one_left u0.le (pow_le_one₀ u0.le (min_le_left ..))).trans (min_le_right ..)
  have total:=prod_le_prod (s:=univ) (fun j _=>(nonneg j).trans (le_max_left ..)) (fun j _=>one j)
  simp only [prod_const,card_univ,Fintype.card_fin,mul_pow,exponent] at total
  exact total.trans (mul_le_mul_of_nonneg_right weight (Real.rpow_nonneg gp.le _))

end YM.Integration.OriginalMarkedRunAction
