import YM.Integration.WilsonPhysicalHistoryRetainedSpringMomentPrice

/-! The same eventual date pays the actual covariance and credit of each
admitted incoming curvature height through the fixed order. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics Pressure
open ConnectedActivityE6 PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open RGLocalTaylor
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem cofinal_moment_price (R : Run G) (simple : G.Simple) (credit : Credit) (d K l : ℕ) {ε η : ℝ}
    (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop, ∀ N n : ℕ,m<N → ∀ {σ W : ℝ},0<σ → σ⁻¹≤zz V (m+1) →
      ∀ o : Target.Order G W,
      WilsonCoherentMayerCovarianceCalendar.deviation G (V.clock.op m n).patch.L o≤
        1+Real.log (betaF G (V.clock.hatBeta m) (V.clock.op m n).patch.L) →
      let C:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      let g:=regulatorRun R.family N n (m+1)
      ∀ (a : PrismA G), a.grade≤d →
        (2:ℝ)^(a.grade-a.rise+1)*C*
          (2*speedPrice G (V.clock.op m n).patch.L o.eta o.gap o.ample ((a.rise+K+2)*(l+1)-1)/σ)^(a.rise+K+2) ≤
            ε*g^(-η) := by
  intro V
  have half : 0<η/2:=by positivity
  have fees (h : Fin (d+1)):=cofinal_speed R simple ((h.val+K+2)*(l+1)-1) (h.val+K+2) d
    (div_pos ep (by norm_num : (0:ℝ)<3)) half
  filter_upwards [Filter.eventually_all.mpr fees,WilsonVacuumPreResetRenderIncome.original R simple credit half]
    with m cover cash
  intro N n later σ W hs width o paid C g a ha
  have aa : a.rise<d+1:=by have:=a.rankA; omega
  have spent:=cover (⟨a.rise,aa⟩:Fin (d+1)) N n later hs width o paid
  have inc:=cash N n later
  have cprice : C≤3*g^(-(η/2)):=(le_abs_self C).trans inc.2.2.1
  let B:=(2*speedPrice G (V.clock.op m n).patch.L o.eta o.gap o.ample ((a.rise+K+2)*(l+1)-1)/σ)^(a.rise+K+2)
  have B0 : 0≤B:=by
    have M:=(speed_price_pos G (V.clock.op m n).patch.L o.eta o.gap o.ample ((a.rise+K+2)*(l+1)-1)).le
    dsimp only [B]
    positivity
  have degree : (2:ℝ)^(a.grade-a.rise+1) ≤ (2:ℝ)^(d+1):=pow_le_pow_right₀ (by norm_num) (by omega)
  have sharp : (2:ℝ)^(a.grade-a.rise+1)*B ≤ (ε/3)*g^(-(η/2)):=
    (mul_le_mul_of_nonneg_right degree B0).trans spent
  change (2:ℝ)^(a.grade-a.rise+1)*C*B≤_
  calc _ = C*((2:ℝ)^(a.grade-a.rise+1)*B):=by ring
    _ ≤ (3*g^(-(η/2)))*((ε/3)*g^(-(η/2))) := by
          exact mul_le_mul cprice sharp (mul_nonneg (by positivity) B0) (by positivity [inc.1])
    _ = ε*(g^(-(η/2))*g^(-(η/2))) := by ring
    _ = _ := by rw [←Real.rpow_add inc.1]; congr 2; ring

end YM.Integration.OriginalMarkedRunAction
