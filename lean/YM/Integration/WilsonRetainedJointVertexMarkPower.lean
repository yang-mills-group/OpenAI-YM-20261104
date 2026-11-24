import YM.Integration.WilsonCoherentMayerFuelCofactor
import YM.Integration.WilsonCoherentMayerFuelSquare

/-! The actual Gaussian moment used by a marked polynomial in the joint action estimate. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Census Window
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoherentMayerHearing Dict06.Series
open scoped BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
    {P : Teller G} {η r K Y : ℝ}

private theorem coin_power {V : Type*} [Fintype V] [DecidableEq V] (p : Normal.poly V) (k : ℕ) :
    Rise.coin (p^(k+1)) ≤ (Rise.coin p)^(k+1) := by
  induction k with
  | zero => simp
  | succ k prev =>
    have pp := Rise.funds 0 (zero_le_one (α:=ℝ)) (p^(k+1)) p
    change Rise.coin (p^(k+1)*p) ≤ Rise.coin (p^(k+1))*Rise.coin p at pp
    have non : 0 ≤ Rise.coin p := by rw [Rise.metal]; positivity
    rw [pow_succ p, pow_succ (Rise.coin p)]
    exact pp.trans (mul_le_mul_of_nonneg_right prev non)

/-- The expense is homogeneous in the complete signed polynomial, including its mark radii. -/
theorem mark_power (X : Coat T F) (A : Rotator P L η r K Y X) (p : Normal.poly (Eye X)) (k : ℕ) :
    let l := k+1
    let cost := Common.priced (1+payE η r K (tubularPrice G L)) (2*(l*p.totalDegree))
    let B := Rise.coin p*(1+Real.sqrt cost)
    let read := fun z : Air f G => Cloud.paint (fun i => z (tube X i)) p
    0 ≤ B ∧ AEStronglyMeasurable read X.dice ∧
    Integrable (fun z => ‖read z‖^l) X.dice ∧ ∫ z, ‖read z‖^l ∂X.dice ≤ B^l := by
  intro l cost B read
  let powered := fun z : Air f G => Cloud.paint (fun i => z (tube X i)) (p^l)
  have pc (q : Normal.poly (Eye X)) : 0 ≤ Rise.coin q := by rw [Rise.metal]; positivity
  have hbase : 0≤1+payE η r K (tubularPrice G L) := by linarith [A.scale.disc]
  have hcost : 0≤cost := by dsimp only [cost, Common.priced]; positivity
  have powRead (z : Air f G) : ‖powered z‖ = ‖read z‖^l := by
    simp [powered, read]
  have integ := (WilsonCoherentMayerFuelSquare.sampled X A.fullC (p^l)).1
  have square := WilsonCoherentMayerFuelSquare.second X A (p^l) (l*p.totalDegree) (MvPolynomial.totalDegree_pow p l)
  have squared : (∫ z, ‖powered z‖^2 ∂X.dice) ≤ (Rise.coin (p^l)*Real.sqrt cost)^2 := by
    rw [mul_pow, Real.sq_sqrt hcost]
    exact square.2
  have pair := WilsonCoherentMayerFuelCofactor.mixed X powered (fun _ => (1:ℂ))
    (mul_nonneg (pc _) (Real.sqrt_nonneg cost)) (show (0:ℝ)≤1 by norm_num)
    integ.aestronglyMeasurable aestronglyMeasurable_const square.1 (by simp) squared (by simp)
  have bound : (∫ z, ‖read z‖^l ∂X.dice) ≤ Rise.coin (p^l)*Real.sqrt cost := by
    simpa only [powRead, norm_one, mul_one] using pair.2
  have mass : 0≤1+Real.sqrt cost := by linarith [Real.sqrt_nonneg cost]
  have norm_int : Integrable (fun z => ‖read z‖^l) X.dice := by
    have original : Integrable (fun z => ‖powered z‖) X.dice := integ.norm
    simpa only [powRead] using original
  refine ⟨mul_nonneg (pc p) mass, (WilsonCoherentMayerFuelSquare.sampled X A.fullC p).1.aestronglyMeasurable, norm_int, ?_⟩
  have size : Real.sqrt cost ≤ (1+Real.sqrt cost)^l := by
    have large : 1 ≤ 1+Real.sqrt cost := by linarith [Real.sqrt_nonneg cost]
    calc
      _ ≤ 1+Real.sqrt cost := by linarith
      _ ≤ (1+Real.sqrt cost)^k*(1+Real.sqrt cost) := le_mul_of_one_le_left mass (one_le_pow₀ large)
      _ = _ := (pow_succ _ k).symm
  calc
    _ ≤ Rise.coin (p^l)*Real.sqrt cost := bound
    _ ≤ (Rise.coin p)^l*(1+Real.sqrt cost)^l :=
      mul_le_mul (coin_power p k) size (Real.sqrt_nonneg _) (pow_nonneg (pc _) _)
    _ = _ := (mul_pow _ _ _).symm

end YM.Integration.OriginalMarkedRunAction

