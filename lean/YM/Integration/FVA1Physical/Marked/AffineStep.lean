import YM.Integration.FVA1Physical.Marked.AffinePurchase

/-! The complete, support-weighted inherited-vacuum pre-reset estimate on
M7a's actual history. It applies to the chart already linked to the marked
step, and directly selects the genuine complement of the incoming seed. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset
open Progress.DirectedRecipe Height Roof Extra.Iteration Time ThroughLaunch Roost JointLoad
open ConnectedActivityE6 SectorMeasure Finset Extra.Trajectories RG3.Script.Picnic
open AllOrder Transit WheelP Floe Floe.Step.PlanV Qlocal Qlocal.Parabola RGComparison01
open scoped BigOperators Classical Topology

/-- The incoming error is the actual complement of the purchased seed rows.
Every anchored derivative invoice has the original support and weight. -/
theorem inherited_portion {G : Gauge} {n : Side} (R : Rep G n) (M : Set ℕ) {b e : ℝ}
    (h : Burn.Candor R.p R.activities M b e) :
    (Tithe.portion R.activities (fun i => i ∉ M)).EBound R.p e := by
  obtain ⟨u,cap,price⟩ := h.sale
  let w := fun i => if i ∈ M then 0 else u i
  refine ⟨w,fun i => ?_,fun o => ?_⟩
  · by_cases hi : i ∈ M
    · simpa only [Tithe.portion,w,hi,if_pos,not_true_eq_false,if_false] using
        (WilsonStartup.Start.zero_bound (b:=R.p) (o:=(R.activities.reg i).site) (X:=(R.activities.reg i).support) (G:=G))
    · simpa only [Tithe.portion,w,hi,if_false,not_false_eq_true,if_true] using cap i
  have he : (fun i : ℕ => if (R.activities.reg i).site=o then R.p.mass (R.activities.reg i).support (w i) else 0) =
      (fun i => if i ∈ M then 0 else Burn.wallet R.p R.activities u o i) := by
    funext i; by_cases hi : i∈M <;> simp [Burn.wallet,w,hi,BudgetPoint.mass]
  exact he ▸ (price o).2

theorem young_admitted {G : Gauge} (A : Levels G) (m k : ℕ) :
    Burn.young (A.clock.hatBeta m) k ≤ A.clock.allowance m := by
  let y := A.clock.hatBeta m
  have hy : 1 < y := A.fits.delayed m
  change y^(Burn.credit k) ≤ (Real.sqrt y)⁻¹^((11:ℝ)/5)
  rw [Real.sqrt_eq_rpow,← Real.rpow_neg (zero_lt_one.trans hy).le,← Real.rpow_mul (zero_lt_one.trans hy).le]
  apply Real.rpow_le_rpow_of_exponent_le hy.le
  rw [Burn.sale_eq]; have hk : 0 ≤ (Burn.horizon k:ℝ) := Nat.cast_nonneg _
  linarith

/-- At every sufficiently UV stage of every actual marked trajectory, the
same pre-reset guide used by the forced linkage contracts every distinguished
physical input subarray, including the non-seed remainder supplied by M7a.
Its per-scale price is exactly Ocean.fee = turnFee*(v+2)/L. -/
def AffineSteps {G : Gauge} (X : Run G) (slope : ℕ → ℝ) : Prop :=
  ∀ (r : ℕ), ∀ᶠ m in atTop, ∀ {z N n k : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
    {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)},
    Metre X.alloy X.kit X.T path Γ z N n k x → z ≤ m → m < N →
    let A := X.alloy.B.a
    let U := x (m+1)
    let y := A.clock.hatBeta (m+1)
    let size := (A.S.oneStep m n).exact_size
    let f := Ocean.fee X.kit m
    ∃ model : Burn.Seed U (M0 k 0 (A.budget (m+1)) (path (m+1)) (X.T.history N n (m+1)).beta),
      let residual := fun i => i ∉ Set.range model.model
      (Tithe.portion U.activities residual).RegularFamily U.p ∧
      (Tithe.portion U.activities residual).EBound U.p (Burn.young y k) ∧ 0 ≤ f ∧ f ≤ slope (A.clock.J m) ∧
      ∀ (H : Opera.Guide X.alloy.B X.kit.shape N m n U), Opera.Price X.alloy.B X.kit.shape N m n U H →
        Ports.Wet X.kit size H r residual (f*Burn.young y k) ∧
        ∀ Ω : ℕ → Prop, ∀ e, (Tithe.portion U.activities Ω).EBound U.p e →
          e ≤ A.clock.allowance (m+1) → Ports.Wet X.kit size H r Ω (f*e)

set_option maxHeartbeats 650000 in
theorem affine_steps {G : Gauge} (X : Run G) (gauge : G.Simple) {slope : ℕ → ℝ}
    (he : AffineReserve G slope X.metals X.rolls X.alloy X.kit) : AffineSteps X slope := by
  unfold AffineSteps
  intro r
  filter_upwards [Ports.aims X.kit gauge r] with m purchasing z N n k path Γ x track lo hi A U y size f
  have hr := track.1.walk (m+1) (by omega) hi
  have hb : U.beta ∈ RG.Shoot.band A (m+1) := by
    rw [show U.beta = _ from hr.beta]
    exact ((X.T.sticks N n).prices (m+1) (Nat.zero_le _) hi).2
  obtain ⟨model,pr⟩ := hr.stamp
  let residual := fun i => i ∉ Set.range model.model
  have hP : Burn.Candor U.p U.activities (Set.range model.model) (Burn.silver y) (Burn.young y k) := by
    rw [show U.p = _ from hr.truep.point]
    exact pr
  have hsub := inherited_portion U _ hP
  obtain ⟨gates,posted,rate⟩ := he
  have hcost : f ≤ slope (A.clock.J m) := by
    unfold f Ocean.fee
    rw [show Collection.turnFee (A.budget m)=_ from (Rain.jersey (A:=X.alloy) (m:=m)).2.2.2]
    exact rate _ _ (step_paid A m)
  have h0 : 0 ≤ f := by
    obtain ⟨H,_,_⟩ := track.2 m lo hi
    have hs' : Burn.young y k ≤ incomingE G (X.rolls.L (A.clock.J (m+1))) (A.clock.hatBeta m) := by
      unfold incomingE
      rw [← PriceCompiler.beta_eq X.alloy.B.valid m]
      exact young_admitted A (m+1) k
    exact (Ocean.contracts X.kit (H:=H) gates hi posted (visits hr.truep) hb residual _ hsub hs').1
  refine ⟨model,Tithe.portion_regular U.activities U.p hr.truep.valid.labels.regular residual,hsub,h0,hcost,?_⟩
  intro H hH
  have any (Ω : ℕ → Prop) (e : ℝ) (hΩ : (Tithe.portion U.activities Ω).EBound U.p e)
      (ad : e ≤ A.clock.allowance (m+1)) : Ports.Wet X.kit size H r Ω (f*e) := by
    have slack : e ≤ incomingE G (X.rolls.L (A.clock.J (m+1))) (A.clock.hatBeta m) := by
      unfold incomingE
      rw [← PriceCompiler.beta_eq X.alloy.B.valid m]
      exact ad
    have bill := (Ocean.contracts X.kit (H:=H) gates hi posted (visits hr.truep) hb Ω e hΩ slack).2
    exact Ports.boards X.kit size H gates hi hH r purchasing.1 hb purchasing.2.1 (purchasing.2.2 _ hb) Ω bill
  exact ⟨any residual _ hsub (young_admitted A (m+1) k), any⟩

end YM.Integration.FVA1Physical.Marked
