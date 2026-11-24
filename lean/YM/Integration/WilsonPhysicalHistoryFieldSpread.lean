import YM.Integration.WilsonPhysicalHistoryFieldDerivatives

/-! Compare the true ordinary weighted angular word norm to the anchored
periodic kernel seminorm using half of the filed exponential width. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryFieldSpread
open Function Finset Lattice Laurent RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep RG16.Literal RG16.Guarding
open MSbar MSbar.Whisk Push.Uniform WilsonPhysicalHistoryFieldDerivatives
open scoped Classical BigOperators ENNReal
variable {G : Gauge} {n : Side} {r : ℕ}

private theorem displacement (x y : Site n) : separation x y ≤ Lotus.skit n (x-y) := by
  change (Finset.univ.sup fun i : Axis => (Lattice.lift (x-y) i).natAbs) ≤
    ∑ i : Axis, (Lattice.lift (x-y) i).natAbs
  exact Finset.sup_le fun i _ => Finset.single_le_sum
    (f:=fun j : Axis => (Lattice.lift (x-y) j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)

/-- The ordinary physical extent is controlled by the original anchored cover metric. -/
theorem extent_le (z : wire G n) (v : Fin r → Primary n G) :
    Whisk.extent (Whisk.zone (Measuring.chart n G) {z.1} (List.ofFn v)) ≤
    Gorge.wide (lake n _) (Fin.cons z (coordinates G n ∘ v)) := by
  classical
  let t : Fin (r+1) → wire G n := Fin.cons z (coordinates G n ∘ v)
  have locate (x : Site n) (hx : x∈Whisk.zone (Measuring.chart n G) {z.1} (List.ofFn v)) :
      ∃ i, (t i).1=x := by
    rcases Finset.mem_union.mp hx with hx|hx
    · exact ⟨0, (Finset.mem_singleton.mp hx).symm⟩
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      obtain ⟨j,rfl⟩ := (List.mem_ofFn' v c).mp hc
      exact ⟨j.succ, by simp [t,coordinates,Measuring.chart]⟩
  apply Whisk.yard
  intro x hx y hy
  obtain ⟨i,rfl⟩ := locate x hx
  obtain ⟨j,rfl⟩ := locate y hy
  exact (displacement (t i).1 (t j).1).trans (Finset.le_sup
    (f:=fun ij : Fin (r+1) × Fin (r+1) => (lake n _).d (t ij.1) (t ij.2)) (mem_univ (i,j)))

/-- Cost of a fixed polynomial spatial moment at a filed positive width. -/
def fee (b : ℝ) (s : ℕ) : ℝ := (1+(b/2)⁻¹)^s*((s.factorial:ℝ)*Real.exp 1)

theorem fee_nonneg {b : ℝ} (hb : 0<b) (s : ℕ) : 0≤fee b s := by
  unfold fee
  positivity

private theorem scaled {b α : ℝ} (hb : 0<b) (hα : α≤b/2) (s D A : ℕ) (ha : D≤A) :
    Whisk.liftW α s D ≤ fee b s * Real.exp (b*A) := by
  let w := b/2
  let x : ℝ := D
  have w0 : 0<w := half_pos hb
  have x0 : 0≤x := Nat.cast_nonneg _
  have v0 : 0≤w*x := mul_nonneg w0.le x0
  have di : w⁻¹*(w*x)=x := by rw [←mul_assoc,inv_mul_cancel₀ w0.ne',one_mul]
  have hy : 1+x ≤ (1+w⁻¹)*(1+w*x) := by
    nlinarith only [v0, inv_nonneg.mpr w0.le, di]
  have hp : (1+w*x)^s ≤ (s.factorial:ℝ)*Real.exp (1+w*x) := by
    simpa only [mul_comm (Real.exp _)] using
      ((div_le_iff₀ (by exact_mod_cast Nat.factorial_pos s : (0:ℝ)<s.factorial)).mp
        (Real.pow_div_factorial_le_exp (1+w*x) (by linarith only [v0]) s))
  have small : (1+x)^s ≤ (1+w⁻¹)^s*((s.factorial:ℝ)*Real.exp (1+w*x)) := by
    calc
      _ ≤ ((1+w⁻¹)*(1+w*x))^s := pow_le_pow_left₀ (by linarith only [x0]) hy s
      _ = _ := mul_pow .. 
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (pow_nonneg (by positivity) _)
  have xa : x ≤ (A:ℝ) := Nat.cast_le.mpr ha
  have expCost : Real.exp (1+w*x)*Real.exp (α*x) ≤ Real.exp 1 * Real.exp (b*A) := by
    rw [← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
    have e := mul_le_mul_of_nonneg_right hα x0
    have t := mul_le_mul_of_nonneg_left xa hb.le
    dsimp [w]
    linarith only [e,t]
  change (1+x)^s*Real.exp (α*x) ≤ _
  calc
    _ ≤ ((1+w⁻¹)^s*((s.factorial:ℝ)*Real.exp (1+w*x)))*Real.exp (α*x) :=
      mul_le_mul_of_nonneg_right small (Real.exp_pos _).le
    _ = ((1+w⁻¹)^s*(s.factorial:ℝ))*(Real.exp (1+w*x)*Real.exp (α*x)) := by ring
    _ ≤ ((1+w⁻¹)^s*(s.factorial:ℝ))*(Real.exp 1*Real.exp (b*A)) :=
      mul_le_mul_of_nonneg_left expCost (by positivity)
    _ = _ := by unfold fee; dsimp [w]; ring

theorem spread {b α : ℝ} (hb : 0<b) (hα : α≤b/2) (s : ℕ)
    (z : wire G n) (v : Fin r → Primary n G) :
    Whisk.spread (Measuring.chart n G) {z.1} α s (List.ofFn v) ≤
      fee b s * Real.exp (b*Gorge.wide (lake n _) (Fin.cons z (coordinates G n ∘ v))) :=
  scaled hb hα s _ _ (extent_le z v)

end YM.Integration.WilsonPhysicalHistoryFieldSpread

