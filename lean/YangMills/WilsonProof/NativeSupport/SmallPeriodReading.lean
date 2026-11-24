import YangMills.WilsonProof.NativeSupport.SmallPeriod

/-! A direct estimate on the actual absolute sum, also at off-calibration
temperatures, whenever the terminal side is bounded by the fixed arity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson RGComparison.Core16
open WilsonUniformUnmarkedInletConnectedCovariance WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletBondRemainder
open scoped Classical BigOperators
variable {G : Gauge} {A : Levels G} {k N per : ℕ}

theorem small_reading (T : Slices A per) (hk : k ≤ N) (β v : ℕ→ℝ)
    {φ : Config G (A.S.side N per)→ℝ} (test : Continuous φ) (sym : GaugeInvariant φ)
    {S : ℝ} (unit : ∀ U,|φ U| ≤ S) {m : ℕ} (side : (A.S.side k per).val ≤ m)
    (top : v (traversal T hk).depth=0) {η : ℝ} (hη : 0 ≤ η)
    (offset : ∀ j,0<j → j<(traversal T hk).depth → |v j| ≤ η) :
    let d:=traversal T hk
    |mean d (WilsonUniformUnmarkedInletSignedResponse.line β v 1) φ 1-mean d β φ 1| ≤
      η*((d.depth*((m*scale d)^4*4) : ℕ)*((A.clock.kernel.penalty*2)*(2*S))) := by
  intro d
  let ok:=traversal_ok T hk
  have line : WilsonUniformUnmarkedInletSignedResponse.line β v 1=β+v := by
    funext j; change β j+1*v j=β j+v j; ring
  have value (γ : ℕ → ℝ) : d.conditioned γ φ 1=mean d γ φ 1 := fraction d ok γ 1 test sym
  rw [line,←value (β+v),←value β]
  obtain ⟨r,_,eq⟩:=WilsonUniformUnmarkedInletConnectedShift.shift d ok β v 1 test sym
  rw [eq,WilsonUniformUnmarkedInletBondCovariances.centered d ok β v top 1 test r]
  change |∑ q∈interior d,v (lag d q)*picture d β v 1 φ r q| ≤ _
  calc _ ≤ ∑ q∈interior d,|v (lag d q)*picture d β v 1 φ r q| := abs_sum_le_sum_abs ..
       _ ≤ ∑ q∈interior d,η*|picture d β v 1 φ r q| := by
            apply sum_le_sum
            intro q hq
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right
              (offset _ (mem_filter.mp hq).2.1 (mem_filter.mp hq).2.2) (abs_nonneg _)
       _ = _ := (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (small_absolute T hk β v r test sym unit side) hη

end YM.Integration.InletSusceptibility.Packet
