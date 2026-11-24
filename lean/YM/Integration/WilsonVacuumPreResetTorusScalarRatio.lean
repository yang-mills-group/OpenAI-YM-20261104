import YM.Integration.WilsonVacuumPreResetTorusScalarClock

/-! Relative errors of the inverse temperature and of the actual adjacent
coupling use the same preassigned kinetic coin as the original course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusScalarRatio
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Tree
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.alloy.B.a

open WilsonVacuumPreResetTorusScalarClock

private theorem change {β B:ℝ}(pos:0<β)(room:β/2≤B):
    0<B ∧ |β/B-1|≤2*ConnectedActivityE6.Coat.gStep β^2*|β-B| ∧
      |ConnectedActivityE6.Coat.gStep B/ConnectedActivityE6.Coat.gStep β-1|≤
        2*ConnectedActivityE6.Coat.gStep β^2*|β-B|:=by
  have bp:0<B:=by linarith
  have p:=Real.sqrt_pos.2 pos
  have b:=Real.sqrt_pos.2 bp
  have ps:=Real.sq_sqrt pos.le
  have bs:=Real.sq_sqrt bp.le
  have gs:ConnectedActivityE6.Coat.gStep β^2=β⁻¹:=by
    rw [ConnectedActivityE6.Coat.gStep,inv_pow,ps]
  have cap:|β-B|/B≤2*ConnectedActivityE6.Coat.gStep β^2*|β-B|:=by
    rw [gs,div_le_iff₀ bp]
    have real:β≤2*B:=by linarith
    calc
      |β-B|=(2*β⁻¹*|β-B|)*(β/2):=by field_simp
      _≤_:=mul_le_mul_of_nonneg_left room (by positivity)
  refine ⟨bp,?_,?_⟩
  · rw [show β/B-1=(β-B)/B by field_simp,abs_div,abs_of_pos bp]
    exact cap
  · have money:ConnectedActivityE6.Coat.gStep B/ConnectedActivityE6.Coat.gStep β-1=
          (β-B)/(√B*(√β+√B)):=by
      unfold ConnectedActivityE6.Coat.gStep
      field_simp
      nlinarith only [ps,bs]
    rw [money,abs_div,abs_of_pos (by positivity :0<√B*(√β+√B))]
    refine (div_le_div_of_nonneg_left (abs_nonneg _) bp ?_).trans cap
    nlinarith only [bs,mul_nonneg b.le p.le]

theorem original (simple:G.Simple)(q:ℕ){ε:ℝ}(earned:0<ε):
    ∀ᶠ j:ℕ in atTop,∀ {N b per k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
      {H:(i:ℕ)→RG.Rep G ((A).S.side i per)},
      Concourse R.alloy R.kit R.T π Γ b N per k H→b≤j→j<N→q+1≤Burn.horizon k→
      let β:=(R.T.history N per j).beta
      let B:=forecast R Γ N per j k
      let g:=ConnectedActivityE6.Coat.gStep β
      0<B ∧ |β-B|≤ε*g^q ∧ |β/B-1|≤ε*g^(q+2) ∧
        |ConnectedActivityE6.Coat.gStep B/g-1|≤ε*g^(q+2):=by
  let levels:=R.alloy.B.a
  let c:ℝ:=2^(q+5)
  have cp:0<c:=by positivity
  have grow:Tendsto levels.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (levels.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have near:Tendsto (fun j=>Clock.gap (levels.clock.hatBeta j)) atTop (𝓝 0):=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp grow)
  have price:Tendsto (fun j=>c*(2*Clock.gap (levels.clock.hatBeta j))) atTop (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=c)).mul ((tendsto_const_nhds (x:=(2:ℝ))).mul near)
  have margin:0 < min (ε/2) (1/2:ℝ):=lt_min (by positivity) (by norm_num)
  filter_upwards [grow.eventually_ge_atTop (8:ℝ),price.eventually_lt_const margin] with j core small
  intro N b per k π Γ H course early live sold β B g
  have band:β∈RG.Shoot.band A j:=((R.T.sticks N per).prices j (Nat.zero_le _) live.le).2
  have covered:=trial_in band
  have base:2≤β:=by linarith only [covered.1,core]
  have bp:0<β:=by linarith
  have gp:0<g:=inv_pos.2 (Real.sqrt_pos.2 bp)
  have weak:g≤1:=by
    rw [show g=(√β)⁻¹ by rfl,inv_le_one₀ (Real.sqrt_pos.2 bp)]
    exact Real.one_le_sqrt.2 (by linarith)
  have scalar:c*g ≤ min (ε/2) (1/2:ℝ):=
    (mul_le_mul_of_nonneg_left (band_gap _ _ (by linarith) covered).2 cp.le).trans small.le
  have rate:=WilsonVacuumPreResetTorusScalarClock.original R course early live sold
  have paid:|β-B|≤(c*g)*g^q:=by
    simpa only [c,Nat.add_assoc,pow_succ,mul_assoc,mul_left_comm,mul_comm] using rate
  have net:|β-B|≤ε/2*g^q:=paid.trans
    (mul_le_mul_of_nonneg_right (scalar.trans (min_le_left ..)) (pow_nonneg gp.le _))
  have absHalf:|β-B|≤1/2:=by
    refine paid.trans ?_
    exact (mul_le_mul (scalar.trans (min_le_right ..)) (pow_le_one₀ gp.le weak) (by positivity)
      (by norm_num :0≤(1/2:ℝ))).trans_eq (mul_one _)
  have legal:=change bp (by linarith only [le_abs_self (β-B),absHalf,base] :β/2≤B)
  have finish:2*g^2*|β-B|≤ε*g^(q+2):=calc
    _≤2*g^2*(ε/2*g^q):=mul_le_mul_of_nonneg_left net (by positivity)
    _=ε*g^(q+2):=by rw [pow_add]; ring
  exact ⟨legal.1,net.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)),
    legal.2.1.trans finish,legal.2.2.trans finish⟩

end YM.Integration.WilsonVacuumPreResetTorusScalarRatio
