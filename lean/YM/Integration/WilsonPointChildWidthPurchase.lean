import YM.Integration.WilsonPointChildFiledPress
import YM.Integration.WilsonPinnedWidthCalendar

/-! Prices of the actual submitted spatial widths and the finite source
    clock on the same Wilson election. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildWidthPurchase
open YM FormalBulk08 Lattice Wilson RG Source Labels Next PhysicalNext.Repeat.Legato Filter
open Borough Dove Next.Foundations WilsonPointChildFiledPress WilsonPinnedWidthCalendar
open scoped Topology Classical
variable {G:Gauge}

theorem prices (R:Run G){orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)(j:ℕ):
    let A:=R.family.path.levels
    0<width R j ∧ width R j≤1 ∧ (width R j)⁻¹≤room R j ∧
      max 1 (ageZ (A.clock.hatBeta j)) ≤ RG16.Lambda A j:=by
  let A:=R.family.path.levels
  let K:=A.clock.kernel
  let W:=Primer.FamilyWindow R.family
  have duty:Evergreens K Spigot.herald R.family.labels.level R.family.params (chart G) W A:=(WilsonWindowFormalAnnouncement.on_run R granted).power
  obtain ⟨B,_,Bz,paid⟩:=duty.payment j
  have t:=A.fits.mono (Nat.le_succ j)
  have widthInv: (width R j)⁻¹ ≤ ageZ (A.clock.hatBeta j):=
    (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans ((paid.header (A.clock.J j) t).trans Bz))
  have above:1≤Real.log (A.clock.hatBeta j):=by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (duty.beta j)
  have logup:0<Real.log (A.clock.hatBeta j):=zero_lt_one.trans_le above
  have slope:Real.log (Real.log (A.clock.hatBeta j))≤Real.log (2+Real.log (A.clock.hatBeta j)):=
    Real.log_le_log logup (le_add_of_nonneg_left (by norm_num))
  refine ⟨W.pos _,(W.lines (le_refl (A.clock.J j)) (Nat.le_succ _)).1.trans (window_le G K _),widthInv.trans ?_,max_le ?_ ?_⟩
  · change 1+Real.log (Real.log (A.clock.hatBeta j))≤1+Real.log (2+Real.log (A.clock.hatBeta j))
    exact add_le_add_right slope 1
  · change 1≤2+Real.log (A.clock.hatBeta j)
    linarith
  · change 1+Real.log (Real.log (A.clock.hatBeta j))≤2+Real.log (A.clock.hatBeta j)
    linarith only [Real.log_le_self logup.le]

end YM.Integration.WilsonPointChildWidthPurchase
