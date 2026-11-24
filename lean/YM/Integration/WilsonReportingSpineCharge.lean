import YM.Integration.WilsonReportingDensityProbes
import YM.Integration.WilsonReportingUpperChartPrice
import YM.Integration.WilsonReportingFactorySingleton

/-! A finite physical test bill for returning the very same filed singleton
along the genuine displaced spine from an arbitrary upper cutoff. The measured
tape on the spine comes from its actual paid Group, and the comparison tape
comes from the signed physical factory at the reporting date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingSpineCharge
open Function Filter Lattice Wilson RG Source RG12 RG05Readout Address Native
open Extra.Histories Trace.Physical Push.Local
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} (hC:C.Makes) {d m N per b:ℕ}
variable {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d}

def charge (t:Letter d) (x:C.label (kept t)) (m N per:ℕ) (U:Emblems C d)
    (V:Sight C d per) (i:Letter d) (j:Probe G (kept i)) : ℂ :=
  let R:=C.path.rep N per m
  let y:=WilsonReportingUpperChartPrice.returned hC t x U m N per
  let q:=WilsonReportingFactorySingleton.row hC (kept t) m N per x
  let fitted:=glyph (readJ t 0) (invoice q 0 (C.localSection (kept t)) R)
  Germ.jet C.params j R.p.threshold 0
    (Juniper.Caret.ratio R (((V m y) (Native.line i)).1-(fitted (Native.line i)).1))

theorem price (simple:G.Simple) (d:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ {N per b:ℕ} {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d},
    Spine D B hC b per d N V U → ∀ (t:Letter d) (x:C.label (kept t)),
    (∀i:Letter d,C.ref (kept i) ≤ m) → C.ref d ≤ m → b ≤ m → m ≤ N → ∀ bill:Letter d→ℝ,
    (∀i,0 ≤ bill i) → (∀i,∀ j∈WilsonReportingDensityProbes.tests C i,
      ‖charge hC t x m N per U V i j‖ ≤ bill i) →
    size (WilsonReportingUpperChartPrice.returned hC t x U m N per)  ≤ 
      2*mass C (kept t) x + ∑ i:Letter d,WilsonReportingDensityProbes.gain C i*bill i := by
  filter_upwards [WilsonReportingFactorySingleton.fitted hC simple d] with m factory
  intro N per b D B V U spine t x aged order start live bill pos paid
  let y:=WilsonReportingUpperChartPrice.returned hC t x U m N per
  let z:=WilsonReportingFactorySingleton.measured hC t x m N per
  obtain ⟨a,actual⟩:=(spine.legal m start live).capacity0 y
  have centered:=WilsonReportingFactorySingleton.printed hC (per:=per) t (aged t) live x
  have diff: size (y-z) ≤ ∑ i:Letter d,WilsonReportingDensityProbes.gain C i*bill i :=
    WilsonReportingDensityProbes.price hC actual centered aged live bill pos paid
  exact (size_compare y z).trans (add_le_add (factory t x (aged t) order live) diff)

theorem affordable (simple:G.Simple) (d e:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ {N per b:ℕ} {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d},
    Spine D B hC b per d N V U → ∀ (t:Letter d) (x:C.label (kept t)),
    (∀i:Letter d,C.ref (kept i) ≤ m) → C.ref d ≤ m → b ≤ m → m ≤ N → ∀ bill:Letter d→ℝ,
    (∀i,0 ≤ bill i) → (∀i,∀ j∈WilsonReportingDensityProbes.tests C i,
      ‖charge hC t x m N per U V i j‖ ≤ bill i) →
    let β:=C.path.levels.clock.hatBeta m
    mass C (kept t) x ≤ β^e → (∑ i:Letter d,WilsonReportingDensityProbes.gain C i*bill i) ≤ β^e →
    size (WilsonReportingUpperChartPrice.returned hC t x U m N per) ≤ β^(e+1) := by
  filter_upwards [price hC simple d,(Next.Rank.Station.hat_rate C.path.levels simple).eventually_ge_atTop 3] with m offer high
  intro N per b D B V U spine t x aged order start live cash cashpos paid β source remainder
  have total:=offer spine t x aged order start live cash cashpos paid
  have positive:0 ≤ β^e:=pow_nonneg ((by norm_num : (0:ℝ) ≤ 3).trans high) _
  calc
    _ ≤ 2*mass C (kept t) x + ∑ i:Letter d,WilsonReportingDensityProbes.gain C i*cash i := total
    _ ≤ 2*β^e+β^e := add_le_add (mul_le_mul_of_nonneg_left source (by norm_num)) remainder
    _ = 3*β^e := by ring
    _ ≤ β*β^e := mul_le_mul_of_nonneg_right high positive
    _ = _ := by rw [pow_succ,mul_comm]


/-- The priced coarse input goes back to the prescribed actual bare
factory column, including its original cutoff/period coordinates. -/
theorem carried (live:m ≤ N) (t:Letter d) (x:C.label (kept t)) :
    Many.point U (WilsonReportingUpperChartPrice.returned hC t x U m N per) m N =
      chunk t (WilsonReportingFactorySingleton.upper hC (kept t) m N per x) := by
  rw [Many.weave_fine live,WilsonReportingUpperChartPrice.returned,Many.point,
    dif_neg (Nat.not_lt.mpr live),LinearEquiv.apply_symm_apply]
  rfl


/-- Each selected genuine probe may quote one fixed power. The finite
basis price is absorbed once before every ultraviolet cutoff and period. -/
theorem probes (simple:G.Simple) (d e:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ {N per b:ℕ} {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d},
    Spine D B hC b per d N V U → ∀ (t:Letter d) (x:C.label (kept t)),
    (∀i:Letter d,C.ref (kept i) ≤ m) → C.ref d ≤ m → b ≤ m → m ≤ N →
    let β:=C.path.levels.clock.hatBeta m
    mass C (kept t) x ≤ β^e → (∀i,∀j∈WilsonReportingDensityProbes.tests C i,
      ‖charge hC t x m N per U V i j‖ ≤ β^e) →
    let y:=WilsonReportingUpperChartPrice.returned hC t x U m N per
    Many.point U y m N=chunk t (WilsonReportingFactorySingleton.upper hC (kept t) m N per x) ∧
      size y ≤ β^(e+1) := by
  let w:=∑ i:Letter d,WilsonReportingDensityProbes.gain C i
  filter_upwards [price hC simple d,(Next.Rank.Station.hat_rate C.path.levels simple).eventually_ge_atTop (2+w)] with m offer enough
  intro N per b D B V U spine t x aged order start live β initial paid y
  have pos:0 ≤ β^e:=pow_nonneg ((C.path.levels.fits.delayed m).le.trans' zero_le_one) _
  have total:=offer spine t x aged order start live (fun _=>β^e) (fun _=>pos) paid
  refine ⟨carried hC live t x,?_⟩
  calc
    _ ≤ 2*mass C (kept t) x + ∑ i:Letter d,WilsonReportingDensityProbes.gain C i*β^e := total
    _ ≤ 2*β^e+w*β^e := by
      dsimp only [w]
      rw [Finset.sum_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left initial (by norm_num : 0 ≤ (2:ℝ))) le_rfl
    _ = (2+w)*β^e := (add_mul ..).symm
    _ ≤ β*β^e := mul_le_mul_of_nonneg_right enough pos
    _ = _ := by rw [pow_succ,mul_comm]

end YM.Integration.WilsonReportingSpineCharge
