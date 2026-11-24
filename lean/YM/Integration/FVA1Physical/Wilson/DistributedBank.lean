import YM.Integration.FVA1Physical.Wilson.PurchasedColumn
import YM.MSbar.Geneva.Cash

/-! A spatially extensive interacting action in the joint Wilson chart. Both
the chart Jacobian and the exact blocking source are included, and every
incoming coefficient is taken from the original selected scene. The price
precedes the period, forest, tags and individual action row. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function Finset Lattice RG YM.Wilson Exterior Tree Precision RGComparison.Core16
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Measuring MSbar.CrossH MSbar.Parma MSbar.Tramp MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure
open scoped Classical Topology
variable {G : Gauge}

/-- Stamping a forest coordinate back onto its actual link has a bound
independent of the period, the forest and the spatial exponential weight. -/
theorem stamp_all_periods {c f : Side} {S : StepData c f} (F : Forest S.ratio)
    {a : ℝ} (ha : 0≤a) (s : ℕ) :
    Syrup (Measuring.chart f G) (address F G) a s (taps F G) (goalK G (Geneva.spire 1 s) 1) := by
  have b:=Geneva.pillars (X:=id) tendsto_id s 1 zero_lt_one
  exact bookF _ _ _ (le_refl (1+a+a+1+1)) zero_lt_one ha b.1 zero_le_one zero_le_one b.2
    (clap F _) (starM G f) (Push.Uniform.town F)

/-- The distributed inherited Wilson input, with the full Haar and blocking
terms. Subpower cost holds in every rooted weighted absolute derivative row. -/
theorem distributed_action (J : Voice G) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (p s m : ℕ)
    {ε : ℝ} (he : 0<ε) :
    ∀ᶠ x:ℝ in atTop, ∀ A : Mosaic.Issue G,
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      let bank:=barbed A.F A.v χ A.T
      Kind bank ∧ ∀ i≤p, Tokew (address A.F G) (αm y) s m 0 (PowerSeries.coeff i bank) (y^ε) ∧
        (PowerSeries.coeff i bank).totalDegree ≤ i+2 := by
  obtain ⟨I⟩:=pre_order G H'.width H'.paths P.J K (n:=p+3) (by omega)
  let R:=Ruby.milkB I P χ 1 s m p
  let E:=goalK G (Geneva.spire 1 s) 1
  let y:=fun x:ℝ=>tip G P.L x
  have hy:Tendsto y atTop atTop:=Work.E09.betaF_growth G P.L
  have growth : Mosaic.Run atTop y (fun x=>R+E^(m+1)*(hatW (y x))^(Alto.Dean p)) 0 :=
    (Mosaic.Run.token hy R).addR hy (((Mosaic.Run.stanza hy).Ypow hy (Alto.Dean p)).mulK hy (E^(m+1)))
  filter_upwards [Mosaic.Issue.gate (tendsto_id : Tendsto (fun x:ℝ=>x) atTop atTop) simple tendsto_id P.L m,
    (Alto.broad.comp hy).eventually_ge_atTop 1, growth ε he] with x gate width cost
  intro A patch kernel season v kind plane wedge bank
  have wide : 1≤hatW v:=width
  have width0:=zero_lt_one.trans_le wide
  have theta0 : 0≤αm v:=by unfold αm; positivity
  have small : αm v≤Alto.cWidth v:=gate.2.2.1
  have unit : αm v≤1:=small.trans ((one_div_le_one_div_of_le one_pos
    (one_le_pow₀ wide : 1≤(hatW v)^2)).trans_eq (div_one _))
  have price : R+E^(m+1)*(hatW v)^(Alto.Dean p)≤v^ε := (le_abs_self _).trans cost
  refine ⟨Rolling.well A.F A.v χ A.T kind,?_⟩
  intro i hi
  have haar:=(Ruby.antigen A.F A.v χ s I kernel season.bends hχ 1 theta0 unit p (by omega) m i hi).2
  rw [patch] at haar
  have deg:=(plane.profile i hi)
  have te : Tokew (Measuring.chart A.f G) (αm v) s m 0 (PowerSeries.coeff i A.T)
      (Alto.purse Alto.Dean (hatW v) i) :=
    Tokew.soft (Tin.weightTok width0 wide ((wedge.shares i hi).aspires width0 (by simpa using deg) m)) small theta0
  have bound:=Ruby.blunt A.F A.v χ A.T s haar te (stamp_all_periods A.F theta0 s) theta0
  refine ⟨Tokew.delta bound le_rfl (le_trans ?_ price),?_⟩
  · change R+E^(m+1)*(hatW v)^(Alto.Dean i) ≤ R+E^(m+1)*(hatW v)^(Alto.Dean p)
    have e0 : 0≤ E := zero_le_one.trans (stamp_all_periods (G:=G) A.F theta0 s).cash
    exact add_le_add_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ wide (Alto.ranked hi)) (pow_nonneg e0 _)) _
  simpa only [one_mul] using (Parma.expanseB A.F A.v χ p A.T plane).profile i hi

end YM.Integration.FVA1Physical.Wilson
