import YM.RG05Readout.Harvest.Report
import YM.RG12.Common.Short

/-! Reexpress a column filed at the reporting date as its actual ultraviolet
factory coordinate, then bring it back through the purchased marked spine.
The resulting price is uniform in the period and records the entire mesh span. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUpperChartPrice
open Function Filter Lattice RG Source RG12 RG05Readout Address Native Harvest
open scoped Classical Topology
variable {G : Gauge} {C : Family G} (hC : C.Makes)

theorem bare {d m N per : ℕ} (aged : C.ref d ≤ m) (live : m ≤ N) (x : C.label d) :
    mass C d ((C.factory d N per).terminal.symm (atK C hC d m (N,per) x)) ≤
      C.S.a m / C.S.a N * mass C d x := by
  let i : UVIndex := (N,per)
  let v := atK C hC d m i x
  have below : charts C hC d m i v = x := (charts C hC d m i).apply_symm_apply x
  have top : charts C hC d N i v = (C.factory d N per).terminal.symm v := by
    rw [charts,dif_pos ⟨aged.trans live,le_rfl⟩]
    change ((C.factory d N per).entries N ((C.factory d N per).terminal.symm v)).x = _
    rw [(hC.calibrated d N per (aged.trans live)).bare_coord]
  have step := (RG12.Commission.line hC (p:=i) aged live le_rfl v).2
  rw [below,top] at step
  exact step

variable {b d m N per : ℕ} {D : Rail C} {B : ℕ → ℕ → ℝ}
    {V : Sight C d per} {U : Emblems C d}

def returned (t : Letter d) (x : C.label (kept t)) (U : Emblems C d) (m N per : ℕ) :
    Palette C d :=
  Many.point U (chunk t ((C.factory (kept t) N per).terminal.symm
    (atK C hC (kept t) m (N,per) x))) N m

theorem signed (spine : Spine D B hC b per d N V U) (t : Letter d) (x : C.label (kept t))
    (aged : C.ref (kept t) ≤ m) (started : b ≤ m) (live : m ≤ N) :
    size (returned hC t x U m N per) ≤
      stringCost C live * (C.S.a m / C.S.a N)^(d+1) * mass C (kept t) x := by
  let y := (C.factory (kept t) N per).terminal.symm (atK C hC (kept t) m (N,per) x)
  let r := C.S.a m / C.S.a N
  have h := Spine.downsized hC spine started live le_rfl (chunk t y)
  change size ((finer U live).symm (chunk t y)) ≤
    advanceCost C d live * size (chunk t y) at h
  rw [size_chunk] at h
  rw [returned,Many.point,dif_neg (Nat.not_lt.mpr live)]
  calc
    _ ≤ advanceCost C d live * mass C (kept t) y := h
    _ ≤ advanceCost C d live * (r * mass C (kept t) x) :=
      mul_le_mul_of_nonneg_left (bare hC aged live x) (advanceCost_pos live).le
    _ = _ := by rw [advanceCost,pow_succ]; dsimp [r]; ring

theorem short_window {e u : ℕ} :
    ∀ᶠ m : ℕ in atTop, ∀ {N per b d : ℕ} {D : Rail C} {B : ℕ → ℕ → ℝ}
      {V : Sight C d per} {U : Emblems C d},
      Spine D B hC b per d N V U → ∀ (t : Letter d) (x : C.label (kept t)),
      C.ref (kept t) ≤ m → b ≤ m → m ≤ N →
      C.S.a m / C.S.a N ≤ (C.path.levels.clock.hatBeta m)^u →
      mass C (kept t) x ≤ (C.path.levels.clock.hatBeta m)^e →
      size (returned hC t x U m N per) ≤ (C.path.levels.clock.hatBeta m)^(u*(d+2)+e) := by
  filter_upwards [string_paid (C:=C) (show 0 < (1:ℝ) by norm_num)] with m priced
  intro N per b d D B V U spine t x aged started live mesh filed
  let r := C.S.a m / C.S.a N
  let β := C.path.levels.clock.hatBeta m
  have rp : 0 ≤ r := (div_pos (C.S.a_pos _) (C.S.a_pos _)).le
  have bp : 0 ≤ β := zero_le_one.trans (C.path.levels.fits.delayed m).le
  have ratio : Real.exp (C.S.scale N-C.S.scale m) = r := by
    have unit (i : ℕ) : Real.exp (C.S.scale i) = (C.S.a i)⁻¹ :=
      Real.exp_log (inv_pos.mpr (C.S.a_pos i))
    rw [Real.exp_sub,unit,unit]
    dsimp [r]
    field_simp [(C.S.a_pos m).ne',(C.S.a_pos N).ne']
  have cost : stringCost C live ≤ r := by simpa only [one_mul,ratio] using priced N live
  calc
    _ ≤ stringCost C live * r^(d+1) * mass C (kept t) x := signed hC spine t x aged started live
    _ ≤ r^(d+2) * mass C (kept t) x := by
      apply mul_le_mul_of_nonneg_right _ (mass_nonneg ..)
      simpa only [pow_succ r (d+1),mul_comm r] using mul_le_mul_of_nonneg_right cost (pow_nonneg rp (d+1))
    _ ≤ (β^u)^(d+2) * β^e := mul_le_mul (pow_le_pow_left₀ rp mesh _) filed
      (mass_nonneg ..) (pow_nonneg (pow_nonneg bp _) _)
    _ = _ := by rw [←pow_mul,←pow_add]

end YM.Integration.WilsonReportingUpperChartPrice
