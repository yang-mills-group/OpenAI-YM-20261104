import YM.Integration.FVA1Physical.Marked.AffineTrajectory

/-! Identify the contracted marked-history remainder on the precise chart
which transfers the true forced bank to the physical post-reset output. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Height Roof Extra.Iteration Time ThroughLaunch Roost JointLoad
open ConnectedActivityE6 SectorMeasure Extra.Trajectories RG3.Script.Picnic
open AllOrder Transit WheelP Floe Floe.Step.PlanV Qlocal Qlocal.Parabola RGComparison01
open scoped BigOperators Classical Topology

set_option maxHeartbeats 650000 in
theorem linked_affine_high {G : Gauge} (X : Run G) {slope : ℕ → ℝ} (paid : AffineSteps X slope) (q : ℕ) :
    ∀ᶠ m in atTop, ∀ {z N n k : ℕ} {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
      {x : (i : ℕ) → Rep G (X.alloy.B.a.S.side i n)},
      Metre X.alloy X.kit X.T path Γ z N n k x → z ≤ m → m < N → q ≤ Burn.horizon k + 2 →
      let A := X.alloy.B.a
      let p := A.budget m
      let U := x (m+1)
      let size := (A.S.oneStep m n).exact_size
      let gain := 2^q * (Coat.gStep U.beta)^q
      ∃ (model : Burn.Seed U (M0 k 0 (A.budget (m+1)) (path (m+1)) (X.T.history N n (m+1)).beta))
        (H : Opera.Guide X.alloy.B X.kit.shape N m n U),
        let residual := fun i => i ∉ Set.range model.model
        let address := Beam.marquee H p
        Opera.Price X.alloy.B X.kit.shape N m n U H ∧
        Ports.Wet X.kit size H q residual (Ocean.fee X.kit m * Burn.young (A.clock.hatBeta (m+1)) k) ∧
        Meadow.Budget p address.reg
          ((Coast.inherited X.kit size H residual).logRead + (Coast.weeded X.kit size H residual q).logRead)
          ((slope (A.clock.J m) + 2) * gain) ∧
        ∃ transfer : KLink p (address.read (Song.plusone H (Match.staple (H:=H) (J:=H) rfl rfl rfl)
          Chi.canonical (X.alloy.B.kin.alpha N m))) (Time.forecastK A m X.kit.scout U.beta/8)
          (p.supportExponent+1+1) p (x m).activities (Time.quoteHard A m X.kit.book U.beta) p.supportExponent,
          KLink.Last transfer := by
  filter_upwards [paid q] with m price z N n k path Γ x track lo hi depth A p U size gain
  obtain ⟨model,_,_,h0,upper,all⟩ := price track lo hi
  obtain ⟨H,hH,transfer⟩ := track.2 m lo hi
  let residual := fun i => i ∉ Set.range model.model
  have wet := (all H hH).1
  have hy := (A.fits.delayed (m+1)).le
  have band : U.beta ∈ RG.Shoot.band A (m+1) := by
    rw [show U.beta = _ from (track.1.walk (m+1) (by omega) hi).beta]
    exact ((X.T.sticks N n).prices (m+1) (Nat.zero_le _) hi).2
  have hb : 0 < U.beta := (half_pos (zero_lt_one.trans_le hy)).trans_le band.1
  exact ⟨model,H,hH,wet,combined_affine_high hy hb band.2 depth h0 upper wet,transfer⟩

end YM.Integration.FVA1Physical.Marked
