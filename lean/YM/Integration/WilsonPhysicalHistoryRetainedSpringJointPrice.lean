import YM.Integration.WilsonPhysicalHistoryRetainedSpringMomentOrder
import YM.Integration.WilsonRetainedJointVertexChamber

/-! The joint signed receipt uses one genuinely earned appearance of the
spatial and covariance bills for each factor on the original calendar. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics Pressure
open ConnectedActivityE6 PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open Finset RGLocalTaylor
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem joint_loss (n s : ℕ) {g ε η : ℝ} (gp : 0<g) (ep : 0<ε)
    (c : Fin (n+1)→ℝ) (c0 : ∀ j,0≤c j)
    (within : ∀ j,c j≤(min 1 ε/2)*g^(-(η/(n+1:ℕ)))) :
    (2:ℝ)^(n+1)*g^s*(∏ j,c j)≤ε*g^((s:ℝ)-η) := by
  let t:=min 1 ε
  have tp : 0≤t:=le_min zero_le_one ep.le
  have steps : (∏ j,c j)≤(t/2*g^(-(η/(n+1:ℕ))))^(n+1):=by
    simpa only [prod_const,card_univ,Fintype.card_fin] using
      (prod_le_prod (fun j (_ : j∈univ)=>c0 j) (fun j (_ : j∈univ)=>within j))
  have cost : t^(n+1)≤ε:=
    (show t^(n+1)≤t by rw [pow_succ]; exact mul_le_of_le_one_left tp (pow_le_one₀ tp (min_le_left ..))).trans
      (min_le_right ..)
  have thermal : (g^(-(η/(n+1:ℕ))))^(n+1)=g^(-η):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul gp.le]
    congr 1
    have count : ((n+1:ℕ):ℝ)≠0:=by positivity
    field_simp
  have pair : g^s*g^(-η)=g^((s:ℝ)-η):=by rw [←Real.rpow_natCast,←Real.rpow_add gp,sub_eq_add_neg]
  calc _ ≤ (2:ℝ)^(n+1)*g^s*(t/2*g^(-(η/(n+1:ℕ))))^(n+1) :=
          mul_le_mul_of_nonneg_left steps (by positivity)
    _ = t^(n+1)*(g^s*g^(-η)) := by
          rw [mul_pow,thermal,div_pow]
          have two : (2:ℝ)^(n+1)≠0:=by positivity
          field_simp
    _ ≤ _ := by rw [pair]; exact mul_le_mul_of_nonneg_right cost (Real.rpow_nonneg gp.le _)

theorem cofinal_joined_price (R : Run G) (simple : G.Simple) (credit : Credit) (d K n : ℕ)
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
      let cost:=fun j r=>occurrencePrice G S.patch.L o.eta o.gap o.ample (σ j) D (a j) r (n+1)
      (2:ℝ)^(n+1)*g^(K+∑ j,(a j).grade)*(∏ j,max (cost j (a j).rise) (cost j ((a j).rise+K)))≤
       ε*g^(((K+∑ j,(a j).grade:ℕ):ℝ)-η) := by
  intro V
  have e : 0 < min 1 ε/2:=by positivity [lt_min zero_lt_one ep]
  have h : 0<η/(n+1:ℕ):=by positivity
  filter_upwards [cofinal_moment_price R simple credit d 0 n e h,
    cofinal_moment_price R simple credit d K n e h] with m base extra
  intro N per later S g D W σ width scope o paid a cap d0 cost
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per (m+1) later
  apply joint_loss n _ gp ep
  · intro j
    apply le_trans _ (le_max_left ..)
    dsimp only [cost,occurrencePrice]
    have hM:=(speed_price_pos G S.patch.L o.eta o.gap o.ample
      (((a j).rise+2)*(n+1)-1)).le
    positivity [width j]
  · intro j
    apply max_le
    · simpa only [cost,occurrencePrice,Nat.add_zero,D,S,V,g] using
        base N per later (width j) (scope j) o paid (a j) (cap j)
    · exact extra N per later (width j) (scope j) o paid (a j) (cap j)

end YM.Integration.OriginalMarkedRunAction
