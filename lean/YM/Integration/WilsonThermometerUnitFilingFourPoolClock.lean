import YM.Integration.WilsonThermometerUnitFilingFourPoolShell

/-! Prices of the two actual physical length changes on the measured coupling clock. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourPoolClock
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open scoped Topology Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
  {H : (Bel R.family.book).Hierarchy}

def outer (z : Trace.Terrace.Arch R.family) (A : ℕ) (r : ℝ) :=
  r*(wilson z r)⁻¹^A

theorem longer (simple : G.Simple) (bliss : Bliss F l z H) (A : ℕ) :
    Tendsto (outer z A) trail trail := by
  have link := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have small := link.conforms simple
  let c := G.slopeConstant⁻¹/2
  have cp : 0<c := half_pos (inv_pos.mpr (Gauge.slopeConstant_pos simple))
  have lt : c<G.slopeConstant⁻¹ := half_lt_self (inv_pos.mpr (Gauge.slopeConstant_pos simple))
  have clock : Tendsto LogV trail atTop := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have upper := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero A).comp clock).div_const (c^A)
  rw [zero_div] at upper
  have due : ∀ᶠ r in trail, outer z A r ≤ (LogV r^A*Real.exp (-LogV r))/c^A := by
    filter_upwards [self_mem_nhdsWithin,link.positive,small.eventually (ge_mem_nhds zero_lt_one),
      link.running.eventually (le_mem_nhds lt),clock.eventually_ge_atTop 0] with r pos gp gu rate lg
    change 0<r at pos
    have lc : c≤LogV r*wilson z r := le_trans rate
      (mul_le_mul_of_nonneg_left (by nlinarith : wilson z r^2 ≤ wilson z r) lg)
    have inv : (wilson z r)⁻¹ ≤ LogV r/c := by
      apply (le_div_iff₀ cp).2
      rw [mul_comm,← div_eq_mul_inv]
      exact (div_le_iff₀ gp).2 lc
    have exp : Real.exp (-LogV r)=r := by rw [LogV,Real.log_inv,neg_neg,Real.exp_log pos]
    calc outer z A r ≤ r*(LogV r/c)^A :=
           mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 gp.le) inv A) pos.le
         _ = _ := by rw [exp,div_pow]; ring
  have positive : ∀ᶠ r in trail, 0<outer z A r := by
    filter_upwards [self_mem_nhdsWithin,link.positive] with r hr hg
    exact mul_pos hr (pow_pos (inv_pos.mpr hg) _)
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨squeeze_zero' (positive.mono fun _ h=>h.le) due upper,positive⟩

theorem invoice (simple : G.Simple) (bliss : Bliss F l z H) (T : ℕ) :
    ∃ B : ℝ, 1≤B ∧ ∀ᶠ r in trail,
      0<dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r) ∧
      dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T*(wilson z r)^(2*T)≤B := by
  have link := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have small := link.conforms simple
  let k := 2*T+4
  let b := 8 + (G.slopeConstant⁻¹+1) + (k:ℝ)
  have bc : 1≤b := by dsimp [b]; linarith [inv_pos.mpr (Gauge.slopeConstant_pos simple),Nat.cast_nonneg (α:=ℝ) k]
  refine ⟨b^T,one_le_pow₀ bc,?_⟩
  filter_upwards [self_mem_nhdsWithin,(gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,
    link.positive,small.eventually (ge_mem_nhds zero_lt_one),
    link.running.eventually (ge_mem_nhds (lt_add_of_pos_right _ zero_lt_one))] with r rp ru gp gu rate
  change 0<r at rp
  change r<1 at ru
  let g := wilson z r
  have gn : 0<g := gp
  have gu' : g≤1 := gu
  have grew : 0≤Real.log g⁻¹ := Real.log_nonneg ((one_le_inv₀ gn).2 gu')
  have lc : 0≤LogV r := Real.log_nonneg ((one_le_inv₀ rp).2 ru.le)
  have eqn : dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r) =
      8+LogV r+(k:ℝ)*Real.log g⁻¹ := by
    change 8+Real.log (r*g^k)⁻¹=_
    rw [LogV,Real.log_inv,Real.log_mul rp.ne' (pow_pos gn _).ne',Real.log_pow,Real.log_inv,Real.log_inv]
    ring
  rw [eqn]
  have bp : 0<8+LogV r+(k:ℝ)*Real.log g⁻¹ := by positivity
  refine ⟨bp,?_⟩
  have one : Real.log g⁻¹ * g^2 ≤ 1 := by
    calc Real.log g⁻¹*g^2 ≤ g⁻¹*g^2 :=
          mul_le_mul_of_nonneg_right ((Real.log_le_sub_one_of_pos (inv_pos.mpr gn)).trans (by linarith)) (sq_nonneg _)
         _ = g := by field_simp
         _ ≤ 1 := gu'
  have charged : (8+LogV r+(k:ℝ)*Real.log g⁻¹)*g^2≤b := by
    change LogV r*g^2≤G.slopeConstant⁻¹+1 at rate
    have sq : g^2≤1 := pow_le_one₀ gn.le gu'
    dsimp only [b]; nlinarith [mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α:=ℝ) k)]
  change (8+LogV r+(k:ℝ)*Real.log g⁻¹)^T * g^(2*T) ≤ b^T
  rw [pow_mul,← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg bp.le (sq_nonneg _)) charged _

end YM.Integration.WilsonThermometerUnitFilingFourPoolClock
