import YM.Integration.FVA1Physical.Wilson.UniformInputSlack
import YM.Integration.FVA1Physical.Wilson.EnterRows
import YM.Integration.FVA1Physical.Wilson.SceneSourceClock

/-! A rooted coarse output is an admissible input to the next interacting
Wilson block, after the actual coupling change and the native forest read.
The normalization includes this block's full distributed action and vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open scoped Classical Topology BigOperators
variable {G:Gauge}

def inheritedBank (A:Issue G) (m:ℕ) (b:PowerSeries ℝ) (T:Nesting G A.f) :=
  enterRows A (sourceClock m b T)

theorem inherited_field_rows (J:Voice G) (clear:Clear G J) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (simple:G.Simple) (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G)
    (p m h s:ℕ) (hm:1 ≤ m) {η:ℝ} (hη:0 < η) :
    ∀ᶠ x:ℝ in atTop, ∀ (A:Issue G) (b:Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      let depth:=h+2*Whisk.ribbon m (p+1+p)+1
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ (T:Nesting G A.f) (v:PowerSeries ℝ), PowerSeries.coeff 0 v=1 →
        (∀ j ≤ p, |PowerSeries.coeff j v| ≤ Alto.purse Alto.Dean (hatW y) j) →
        (∀ j ≤ p, Vault (Measuring.chart A.f G) {b} (αm y) s depth 0 (PowerSeries.coeff j T) (y^(inputSlack p m h hη / 2 / 2)) ∧
          (PowerSeries.coeff j T).totalDegree ≤ m) →
        ∀ i ≤ p, Vault (address A.F G) {b} (αm y) s h 0
          (PowerSeries.coeff i (normalizedRows A χ (inheritedBank A m v T) p)) (y^η) := by
  let q:=h+2*Whisk.ribbon m (p+1+p)+1
  let ε:=inputSlack p m h hη
  have hε:=inputSlack_pos p m h hη
  have buy:=fixed_input_rows J clear χ hχ simple H H' P K branch p m h s hm hη
  let ε':=ε/2
  have he:0<ε':=half_pos hε
  let gy:=Work.E09.betaF_growth G P.L
  filter_upwards [buy,gy.eventually (clock_vault_subpower s q p m he),
    ((tendsto_rpow_atTop he).comp gy).eventually_ge_atTop (enterFee G s^q),
    (Alto.broad.comp gy).eventually_ge_atTop 1,gy.eventually_gt_atTop 0] with x offer clock reserve large pos
  intro A b patch kernel season y depth kind profile wedge T v unit budget ink i hi
  apply offer A b patch kernel season kind profile wedge _ _ i hi
  intro j hj
  have costs:=clock _ A.f (Measuring.chart A.f G) {b} v T (αm y) unit budget (fun k hk=>(ink k hk).1) j hj
  have bound:Bronze.brim p v (hatW y^Alto.Dean p) :=
    fun k hk=>(budget k hk).trans (pow_le_pow_right₀ large (Alto.ranked hk))
  have deg:=(sourceClock_vault (Measuring.chart A.f G) {b} s q p m T v unit bound (one_le_pow₀ large)
    (fun k hk=>(ink k hk).1) j hj).2
  have a0:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have transfer:=enter_vault A s q j a0 {b} (sourceClock m v T) 0
    (by rw [Matrix.mulVec_zero]; exact costs)
  have room:enterFee G s^q * y^ε' ≤ y^ε := by
    calc enterFee G s^q * y^ε' ≤ y^ε'*y^ε' := mul_le_mul_of_nonneg_right reserve (Real.rpow_nonneg pos.le _)
         _ = y^ε :=by rw [←Real.rpow_add pos];congr 1; dsimp only [ε'];ring
  exact ⟨Quote.widen transfer.1 room le_rfl,transfer.2.trans deg⟩

end YM.Integration.FVA1Physical.Wilson
