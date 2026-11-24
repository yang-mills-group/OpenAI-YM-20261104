import YangMills.WilsonProof.NativeSupport.FrozenCalendar
import YangMills.WilsonProof.NativeSupport.FundedProjection

/-! The quiet forced activity can be made smaller than any prescribed
power of the original top hatted temperature, simultaneously over the
whole eligible inlet. The order is chosen before its original cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice RG Wilson PhysicalNext.Repeat.Legato
open Extra.Histories Push.PriceCompiler
open scoped Classical Topology
variable {G : Gauge}

theorem inlet_forced_clock (R : Run G) (simple : G.Simple) (W q : ℕ) :
    ∀ᶠ k:ℕ in atTop, ∀ t j N, k≤t → t≤j → j≤N →
      R.family.S.scale N-R.family.S.scale t ≤ (W:ℝ)*Real.log (R.alloy.B.a.clock.hatBeta N) →
      let b:=R.alloy.B.a.clock.hatBeta
      b N/2≤b j ∧ Real.sqrt (R.alloy.B.a.clock.forcedAllowance j) ≤ (2/b N)^q := by
  let A:=R.alloy.B.a
  let C:=G.slopeConstant*(W:ℝ)
  have c0 : 0≤C := mul_nonneg (Gauge.slopeConstant_pos simple).le (Nat.cast_nonneg _)
  have rate:=Next.Rank.Station.hat_rate A simple
  obtain ⟨k₁,h₁⟩:=eventually_atTop.mp (rate.eventually_ge_atTop ((4*C)^2))
  obtain ⟨k₂,h₂⟩:=eventually_atTop.mp (rate.eventually (Doors.stain_beats q))
  filter_upwards [eventually_ge_atTop k₁,eventually_ge_atTop k₂] with k height tail
  intro t j N kt tj jN span
  let b:=A.clock.hatBeta
  have b0 : 0<b N := zero_lt_one.trans (A.fits.delayed N)
  have positive:=Real.sqrt_pos.mpr b0
  have s : 4*C≤Real.sqrt (b N) := (Real.le_sqrt (by linarith only [c0]) b0.le).mpr (h₁ N (by omega))
  have reserve : C*Real.log (b N) ≤ b N/2 := by
    have hl:=Real.log_le_sub_one_of_pos positive
    rw [Real.log_sqrt b0.le] at hl
    have a:=mul_le_mul_of_nonneg_left hl c0
    nlinarith only [a,mul_le_mul_of_nonneg_right s positive.le,Real.sq_sqrt b0.le,c0]
  have scaleInc : Monotone A.S.scale := monotone_nat_of_le_succ fun i=>by
    rw [Schedule.scale_succ]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (A.S.block i).property))
  have sep : b N-b j ≤ C*Real.log (b N) := by
    change A.clock.bar+G.slopeConstant*A.S.scale N-(A.clock.bar+G.slopeConstant*A.S.scale j)≤_
    rw [show _+_*(A.S.scale N)-(_+_*A.S.scale j)=G.slopeConstant*(A.S.scale N-A.S.scale j) by ring]
    change _ ≤ (G.slopeConstant*(W:ℝ))*Real.log (b N)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((sub_le_sub_left (scaleInc tj) _).trans span) (Gauge.slopeConstant_pos simple).le
  have half : b N/2≤b j := by linarith only [sep,reserve]
  have bj : 0<b j:=zero_lt_one.trans (A.fits.delayed j)
  have forced : Real.sqrt (A.clock.forcedAllowance j) * (b j)^q ≤ 1 := h₂ j (by omega)
  refine ⟨half,((le_div_iff₀ (pow_pos bj q)).mpr forced).trans ?_⟩
  rw [←one_div_pow]
  exact pow_le_pow_left₀ (by positivity) ((div_le_div_iff₀ bj b0).mpr (by linarith only [half])) q

end YM.Integration.InletSusceptibility.Packet
