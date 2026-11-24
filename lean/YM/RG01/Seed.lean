import YM.RG01.Calendar

/-! # Pay higher seed exponent on the actual schedule from the forced-output bill

The schedule gates in Height.Rich furnish only the numeral 3 in
X^3 ≤ exp(mark). With the schedule fixed, deduce the
fixed-any-order bound by instead spending the actual *forced* budget and graph
preparation inequalities on that schedule. The same estimate pays a sqrt(w)
divisor on unmarked forced output (not a proof for forced outputs with marks
that need their own pricing).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Physical
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Input Time Org Supply
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Greenbelt Match Song
open Roof Roost ThroughLaunch Progress.DirectedRecipe Stock Opera PriceCompiler Pressure.Testing Clock Instrument UVNext.CouplingReset
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (hG : G.Simple) {M : Metals G} {D:Rolls M.p} {A : Alloy M D}
  (X : Factor A) {N m n : ℕ}
local notation "lv"=> A.B.a
local notation "FINE"=> A.B.a.S.side (m+1) n
local notation "XXm" => A.B.a.clock.hatBeta m
local notation "BP"=> (A.B.a.budget m)
local notation "J_f"=> A.B.a.clock.J (m+1)
local notation "J_c"=> A.B.a.clock.J m
local notation "YY"=> X.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
local notation "φ"=> A.B.kin.alpha N m

variable (Q : RG.Rep G (A.B.a.S.side (m+1) n)) (hm:m<N) (hq:Lives A.B.bake N (m+1) n Q) (hx:Q.beta∈band A.B.a (m+1))
local notation "UU"=> M.p.profile (A.B.a.clock.J m)
local notation "GROW_" => grow G (D.L (J_f)) (XXm)

/-- Pressing the funded numeric fee for the weaker goal gives a useful bound
on `forecastK` on this trajectory directly; don't need separate rate-control
hypotheses over the moving stages. -/
lemma forecastK_le (β : ℝ) (hb : β∈band A.B.a (m+1)) :
    0 ≤ forecastK A.B.a m X.scout β ∧
    forecastK A.B.a m X.scout β ≤ A.B.a.clock.forcedAllowance m := by
  let i:= (J_c); let j:= (J_f)
  let x:= (XXm); let y:= (lv).clock.hatBeta (m+1)
  let h := X.machine.shops
  have hcov:= X.machine.coverage j i (step_paid A.B.a m)
  have h' := h _ _ (A.B.valid.pays m) _ (step_paid (lv) m)
  have hu : y=x+G.slopeConstant*Real.log (D.L j).val := by rw [← PriceCompiler.block_eq A.B.valid]; exact (Deployment.hat m).symm
  have hs : M.p.profile i = A.B.a.params m:= (params_eq A.B.valid m).symm
  have hT:= (Deployment.clock_eqns (lv).clock m).2.2.2.2.2.2
  have hB : (BP).B=Clock.cover x:= rfl
  obtain ⟨-,-,hk⟩:=h' (BP) (hs.symm ▸ (show Same (A.B.a.params m) (BP) from ⟨rfl,rfl,rfl⟩)) hB hT
  have hq : |(0:ℝ)| ≤ alphaBound D j:= by
    rw [abs_zero]
    exact add_nonneg (M.p.profile _).drift_ge (abs_nonneg _)
  have he:=hk (X.exchange j i) 0 0 β hq (hu ▸ trial_in hb)
  dsimp only at he
  rw [← hu] at he
  let γ:= Real.exp (-Payments.Pairing.kGoal (X.book j i) y β)
  obtain ⟨u,κ,_,hκ⟩:= he.2.2.1.hard
  let F:=forecastK A.B.a m X.scout β
  let H:=Payments.inflation F u κ
  have h1:= hκ.returns
  have hv:=Real.add_one_le_exp H
  have hp: Real.exp (-κ) * H ≤ γ:= (mul_le_mul_of_nonneg_left
    (le_sub_iff_add_le.mpr hv) (Real.exp_pos _).le).trans h1
  have hr: F ≤ Real.exp (-κ)*H:= by
    calc
      _ = Real.exp (-κ)*(Real.exp κ * F):= by rw [←mul_assoc,←Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ _:= mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (b:=2*u) (mul_nonneg (by norm_num) hκ.soft)) (Real.exp_pos _).le
  exact ⟨hκ.hard,(hr.trans hp).trans ((he.2.2.2 hcov.1).2.trans_eq (Deployment.clock_eqns (lv).clock m).2.2.2.2.1.symm)⟩

lemma armZ {P:Teller G} (Q:YM.ConnectedActivityE6.Target G P)
    (L : Side) (μ x : ℝ) (j : ℕ) (hy : 1 ≤ betaF G x L) :
    (betaF G x L)⁻¹ * Real.exp (-Q.mark L μ x) ≤ Cash.armK Q L μ x 0 j := by
  let y:= betaF G x L
  let K:=Q.costs L μ 1 x 0
  have hv: y⁻¹ ≤ Q.goal L x:= by
    unfold Target.goal
    rw [← Real.rpow_neg_one y]
    exact Real.rpow_le_rpow_of_exponent_le hy (by linarith [Q.start])
  have hk : y⁻¹ ≤ K.rootHit := hv.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hp:=Push.AbsoluteSums.polynomial_cost Q.usable (show (0:ℝ) ≤ 0 from le_rfl) j
  have he : 1 ≤ Reserves.extract Q.ε j 0 0:= by
    simpa only [add_zero,one_pow,mul_zero,sub_zero,Real.exp_zero,mul_one,Reserves.extract,Reserves.polyPrice] using! hp
  have hh0 : 0≤ y⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hy)
  have hh : y⁻¹ ≤ Q.overture L μ x j := by
    unfold Target.overture Target.quantum Mixed.Costs.ceiling
    change y⁻¹ ≤ Reserves.extract Q.ε j 0 (K.markSeed*(0:ℕ)) * Reserves.treeYield K.rootHit _ _
    rw [Nat.cast_zero,mul_zero,Reserves.treeYield,pow_zero,mul_one]
    apply hk.trans
    apply le_trans (b := K.rootHit * ((1-(1/2:ℝ))⁻¹))
    · exact le_mul_of_one_le_right (hh0.trans hk) (by norm_num)
    exact le_mul_of_one_le_left (mul_nonneg (hh0.trans hk) (by norm_num)) he
  have hz:=hh.trans (le_mul_of_one_le_left (hh0.trans hh) (show (1:ℝ)≤20 by norm_num))
  unfold Cash.armK; simp only [pow_zero, inv_one,one_mul]
  rw [mul_comm y⁻¹]
  exact mul_le_mul_of_nonneg_left (hz.trans (le_mul_of_one_le_right (hh0.trans hz) (by norm_num))) (Real.exp_pos _).le

lemma obliged (β : ℝ) (hb : β∈band A.B.a (m+1)) :
    ((lv).clock.hatBeta (m+1))⁻¹ * Real.exp (-(YY).mark (D.L (J_f)) (X.shape.μ (J_f) (J_c)) (XXm))
      ≤ (lv).clock.forcedAllowance m := by
  let j:= J_f; let i:= J_c
  let H:= X.pledging.conducts.income
  have h := H.earns j i (step_paid A.B.a m) _ (A.B.valid.pays m) β (show inBand (betaF G (A.B.a.clock.hatBeta m) (D.L j)) β from by
    rw [← PriceCompiler.beta_eq A.B.valid m]; exact trial_in hb)
  have hz:= forecastK_le X β hb
  have he : 1 ≤ betaF G (XXm) (D.L j):= by
    rw [← PriceCompiler.beta_eq A.B.valid m]; exact ((lv).fits.delayed _).le
  apply le_trans (b:=(1/8 : ℝ)*forecastK (lv) m X.scout β)
  · rw [PriceCompiler.beta_eq A.B.valid m]
    rw [← PriceCompiler.beta_eq A.B.valid m] at h
    exact (armZ (YY) (D.L j) (X.shape.μ j i) (XXm) _ he).trans h
  exact (mul_le_of_le_one_left hz.1 (by norm_num)).trans hz.2

end YM.RG01.Physical
