import YM.RG05Readout.Grants.Grain
import YM.RG12.Canonical.Charts

/-! The full signed primary and its measured germ at the reporting date use a
single physical factory. The same filed coordinate controls every later
ultraviolet cutoff and period, including the genuine finite-volume wrapping. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingFactorySingleton
open Function Filter Lattice Wilson RG Source RG12 RG05Readout Address Native
open Extra.Histories MergeProof.Ribbons
open scoped Classical Topology
variable {G : Gauge} {C : Family G} (hC : C.Makes) {d m N per : ℕ}

/-- Upper coordinate of the physical column filed at date m. -/
def upper (d m N per : ℕ) (x : C.label d) : C.label d :=
  (C.factory d N per).terminal.symm (atK C hC d m (N,per) x)

def row (d m N per : ℕ) (x : C.label d) :=
  (C.factory d N per).entries m (upper hC d m N per x)

theorem coordinate (aged : C.ref d ≤ m) (live : m ≤ N) (x : C.label d) :
    (row hC d m N per x).x = x := by
  let A := charts C hC d m (N,per)
  have entered (v : C.label d) :
      A v = ((C.factory d N per).entries m ((C.factory d N per).terminal.symm v)).x := by
    unfold A
    rw [charts,dif_pos ⟨aged,live⟩]
    rfl
  change ((C.factory d N per).entries m ((C.factory d N per).terminal.symm
    (atK C hC d m (N,per) x))).x = x
  rw [← entered]
  exact A.apply_symm_apply x

theorem signed (aged : C.ref d ≤ m) (live : m ≤ N) (x : C.label d) :
    let q := row hC d m N per x
    let rep := C.path.rep N per m
    q.Format 0 C.params rep ∧ q.x = x ∧
      q.remBound 0 rep (Real.sqrt (C.path.levels.clock.forcedAllowance m))
        ((C.path.levels.params m).columns * mass C d x) := by
  intro q rep
  let z := upper hC d m N per x
  have valid := hC.calibrated d N per (aged.trans live)
  have eqX := coordinate hC (per:=per) aged live x
  refine ⟨valid.format m aged live z,eqX,rem_mono (valid.cap m aged live z) ?_⟩
  change (C.path.levels.params m).columns * (C.labels.level d).coeffSize
    ((C.labels.level d).core (row hC d m N per x).x) ≤ _
  rw [eqX]
  exact mul_le_mul_of_nonneg_left (Work.G08.size_core ..)
    (zero_le_one.trans (C.path.levels.params m).columns_ge)

/-- Measured label of the complete physical reporting column at the selected
angular mark. This line evaluates the actual regular pieces of the signed row. -/
def measured (t : Letter d) (x : C.label (kept t)) (m N per : ℕ) : Palette C d :=
  chunk t (Trace.Physical.Germ.projection (C.labels.level (kept t)) C.params
    (C.path.rep N per m).p.threshold 0 (row hC (kept t) m N per x))

theorem printed (t : Letter d) (aged : C.ref (kept t) ≤ m) (live : m ≤ N)
    (x : C.label (kept t)) :
    let q := row hC (kept t) m N per x
    let rep := C.path.rep N per m
    Printed C d rep 0 (Real.sqrt (C.path.levels.clock.forcedAllowance m))
      (glyph (readJ t 0) (invoice q 0 (C.localSection (kept t)) rep))
      (chunk t x) (measured hC t x m N per) ((C.path.levels.params m).columns * mass C (kept t) x) := by
  intro q rep
  obtain ⟨fmt,eqX,cap⟩ := signed hC (per:=per) aged live x
  have out := printed_one t q fmt cap
  change q.x = x at eqX
  rw [eqX] at out
  exact out

/-- Wrapping costs for the genuine measured coordinate, uniform in the
upper cutoff, are smaller than every prescribed power of the physical mesh. -/
theorem close (simple : G.Simple) (d : ℕ) (K : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ {N per : ℕ} (t : Letter d) (x : C.label (kept t)),
      C.ref (kept t) ≤ m → C.ref d ≤ m → m ≤ N →
      size (measured hC t x m N per - chunk t x) ≤
        Real.exp (-K*C.S.scale m) * mass C (kept t) x := by
  let c := wrap_price d C
  have cp : 0 < c := zero_lt_one.trans_le (price_nn ..)
  have wage := (Note.notes C.S c cp).mills (fuNote C)
  have payable := wage.outweigh (Note.bell_exp C.S 1) (by norm_num)
  filter_upwards [Copper.oversized C.path.levels simple (K+1),payable] with m volume paid
  intro N per t x aged order live
  have receipt := printed hC (per:=per) t aged live x
  obtain ⟨horder,hpower⟩ := Trace.Physical.GermGraph.dimensions d N per m hC order live
  have error := wraps_paid d C receipt horder hpower
  rw [(hC.wilson.represents N per m live).vac] at error
  let a := mass C (kept t) x
  let v := Trace.Physical.Germ.wraps (C.path.levels.budget m) (C.side m per)
  let b := (C.path.levels.params m).columns
  let s := C.S.scale m
  have pay : c*b ≤ Real.exp s := by simpa only [one_mul] using paid
  have exponent : s + -(K+1)*s = -K*s := by ring
  calc
    _ ≤ c*v*(b*a) := error
    _ = (c*b*v)*a := by ring
    _ ≤ (Real.exp s*Real.exp (-(K+1)*s))*a := by
      apply mul_le_mul_of_nonneg_right _ (mass_nonneg ..)
      exact mul_le_mul pay (volume per) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add,exponent]

theorem fitted (simple : G.Simple) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ {N per : ℕ} (t : Letter d) (x : C.label (kept t)),
      C.ref (kept t) ≤ m → C.ref d ≤ m → m ≤ N →
      size (measured hC t x m N per) ≤ 2 * mass C (kept t) x := by
  filter_upwards [close hC simple d 0] with m issued
  intro N per t x aged order live
  have err := issued (per:=per) t x aged order live
  simp only [neg_zero,zero_mul,Real.exp_zero,one_mul] at err
  calc
    _ ≤ size (chunk t x) + size (measured hC t x m N per - chunk t x) := size_compare ..
    _ ≤ mass C (kept t) x + mass C (kept t) x := by
      rw [size_chunk]
      exact add_le_add le_rfl err
    _ = _ := by ring

end YM.Integration.WilsonReportingFactorySingleton
