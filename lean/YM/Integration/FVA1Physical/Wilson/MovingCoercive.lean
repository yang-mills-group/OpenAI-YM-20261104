import YM.Integration.FVA1Physical.Wilson.MovingBarrier
import YM.FVA2.RayScatter
import YM.RGComparison.Core16.Therm.Pulse

/-! The full history/retained-ray action has a strictly positive local
quadratic form after adjoining a single pure square of the ray parameter.
The pure square factors out of the physical integral on the slice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Lattice RG Tree RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FVA2.CityHistory FVA2.RayScatter
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c) (t : d.Tags) (u : Pins G c)

def rayPhase := charge (consume d t 1) 1 u

theorem rayPhase_stationary (h : d.OK G) :
    Stationary (rayPhase d t u) := by
  apply Inherit.stable (charge_hot 1 u (thermal d t h 1))
  · simp [charge, FVA2.RayScatter.tax, thermal_zero d t h 1]
  exact fun x => add_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) (action_nonneg ..)

private theorem joint_second_nonneg (h : d.OK G) (y : SpaceF G d) :
    0 ≤ jet (consume d t 1) 2 y := by
  have s := thermal_stat d t h
  have lo (i : ℕ) (hi : i < 2) : jet (consume d t 1) i y = 0 := by
    interval_cases i
    · rw [jet_zero]; exact s.base0
    exact s.base1 y
  exact ge_of_tendsto (((directions s.smooth y).shift lo).tendsto_first)
    (Eventually.of_forall fun r => mul_nonneg (sq_nonneg _) (action_nonneg ..))

/-- The scalar parameter and all internal coordinates are covered jointly,
including histories of length zero and a vanishing retained direction. -/
theorem rayPhase_coercive (h : d.Room G) :
    ∃ κ > (0:ℝ), ∀ y, κ * ‖y‖^2 ≤ jet (rayPhase d t u) 2 y := by
  let E := Coordinates G d
  let p := consume d t (G:=G) 1
  let L := recover (E:=E) u
  have h0 := room_ok d h
  have hs : ContDiffAt ℝ ω p 0 := thermal d t h0 1
  have tax₂ (y : ℝ × E) : jet (tax (E:=E) 1) 2 y = y.1^2 := by
    simpa only [FVA2.RayScatter.tax, one_mul] using (Therm.double
      (f:=tax (E:=E) 1) (contDiffAt_const.mul (contDiffAt_fst.pow 2)) y
      (fun a => by change 1*(a*y.1)^2=(1*y.1^2)*a^2; ring)).2
  have H (y : ℝ × E) : jet (rayPhase d t u) 2 y = y.1 ^ 2 + jet p 2 (L y) := by
    unfold rayPhase charge
    rw [Inherit.plus (a:=tax 1) _ (contDiffAt_const.mul (contDiffAt_fst.pow 2))
       (((map_zero L).symm ▸ hs : ContDiffAt ℝ ω p (L 0)).comp 0 L.contDiff.contDiffAt),
       tax₂,FVA2.GermLaplace.jet_pull L p (hs.of_le le_top)]
  apply quadratic_min
  intro y hy
  rw [H]
  by_cases hz : y.1 = 0
  · have hp : y.2 ≠ 0 := fun he => hy (Prod.ext hz he)
    have he : L y = (y.2,0) := by ext1 <;> simp [L,recover,hz]
    rw [he,hz,zero_pow (by decide),zero_add]
    have hcore := core_life d t h0 y.2
    have hq := progress d t (G:=G) (y.2,0)
    change (jointV (G:=G) d t).flourish (y.2,0) = _ at hcore
    have he' : 0 < 1+d.edgeBill G := add_pos_of_pos_of_nonneg one_pos (edgeBill_nonneg ..)
    have positive := lt_of_lt_of_le
      (mul_pos (pow_pos (inv_pos.mpr he') 2) (pow_pos (norm_pos_iff.mpr hp) 2))
      (coercive_charge t h y.2)
    change 0 < jet (consume d t 1) 2 (y.2,0)
    linarith only [hcore,hq,positive]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hz) (joint_second_nonneg d t h0 _)

end YM.Integration.FVA1Physical.Wilson
