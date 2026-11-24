import YM.Integration.WilsonFactoryOnShellGlyphs

/-! Exact independent deck expansion of an arbitrary J-field, on the actual
Wilson factory and its joint normalized finite-volume law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryPhysicalGlyphs
open Function Finset Lattice Wilson RG Spec OPE SharpGram RG12 RG17 MS MS.Theater MS.Menus MS.Local.Physical
open MeasureTheory
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} (B : Deck G) (d : ℕ)

def note (q : Glyph B d) : (Spin.comparator C.book).Field d := Pert.RawLabels.enroll C.labels d (WilsonFactoryOnShellGlyphs.primitive B d q)
def weight (a : (Spin.comparator C.book).Field d) (q : Glyph B d) : ℂ :=
  WilsonFactoryOnShellGlyphs.spectrum B d (Pert.RawLabels.physicalLabel C.labels d a) q

variable (J : ℝ → PhysMS.tower S) (r : ℝ) (a : (Spin.comparator C.book).Field d)

theorem chart : J r d a = ∑ q : Glyph B d,weight (C:=C) B d a q • J r d (note (C:=C) B d q) := by
  let A := (J r d).toLinearMap
  have expand : a = ∑ q : Glyph B d, weight (C:=C) B d a q • note (C:=C) B d q :=
    WilsonFactoryOnShellGlyphs.comparator B d C.labels a
  change A a = ∑ q : Glyph B d, weight (C:=C) B d a q • A (note (C:=C) B d q)
  exact (congrArg A expand).trans (by rw [map_sum]; simp only [map_smul])

variable (N p : ℕ) (x : Site (C.side N p))

def mark : Config G (C.side N p) → ℂ := C.O N p (S.representative d (J r d a)) x

theorem visible : Continuous (mark (C:=C) d J r a N p x) := C.continuousO N p d _ x

theorem measured : mark (C:=C) d J r a N p x =
    ∑ q : Glyph B d, weight (C:=C) B d a q • mark (C:=C) d J r (note (C:=C) B d q) N p x := by
  let f := ((C.linearO N p d x).mk' _).comp (S.representative d)
  change f (J r d a) = ∑ q : Glyph B d,weight (C:=C) B d a q • f (J r d (note (C:=C) B d q))
  rw [chart B d J r a,map_sum]
  simp only [map_smul]

theorem read (ζ : Config G (C.side N p) → ℂ) (good : Continuous ζ) :
    C.omega N p (fun U => mark (C:=C) d J r a N p x U * ζ U) =
    ∑ q : Glyph B d, weight (C:=C) B d a q •
      C.omega N p (fun U => mark (C:=C) d J r (note (C:=C) B d q) N p x U * ζ U) := by
  rw [measured B d J r a N p x]
  unfold Family.omega Wilson.moment
  simp_rw [Finset.sum_apply,Pi.smul_apply,Finset.sum_mul,smul_mul_assoc]
  rw [integral_finsetSum]
  · simp only [integral_smul]
  · intro q _
    exact Integrable.smul (weight (C:=C) B d a q) (Wilson.continuous_integrable (C.beta N p)
      ((visible (C:=C) d J r (note (C:=C) B d q) N p x).mul good))

/-- Both radii and positions are independent; the original *one joint
probability* and an arbitrary complete continuous external detector are kept. -/
theorem joint {e : ℕ} (s : ℝ) (b : (Spin.comparator C.book).Field e) (y : Site (C.side N p))
    (ζ : Config G (C.side N p) → ℂ) (good : Continuous ζ) :
    C.omega N p (fun U => mark (C:=C) d J r a N p x U * (mark (C:=C) e J s b N p y U * ζ U)) =
    ∑ q : Glyph B d,weight (C:=C) B d a q • ∑ t : Glyph B e,weight (C:=C) B e b t •
      C.omega N p (fun U => mark (C:=C) d J r (note (C:=C) B d q) N p x U *
        (mark (C:=C) e J s (note (C:=C) B e t) N p y U * ζ U)) := by
  have first := read B d J r a N p x (fun U => mark (C:=C) e J s b N p y U * ζ U)
    ((visible (C:=C) e J s b N p y).mul good)
  refine first.trans ?_
  refine Finset.sum_congr rfl fun q _ => congrArg (weight (C:=C) B d a q • ·) ?_
  have turn := read B e J s b N p y (fun U => mark (C:=C) d J r (note (C:=C) B d q) N p x U * ζ U)
    ((visible (C:=C) d J r _ N p x).mul good)
  calc
    _ = C.omega N p (fun U => mark (C:=C) e J s b N p y U *
      (mark (C:=C) d J r (note (C:=C) B d q) N p x U * ζ U)) := congrArg (C.omega N p) (funext fun _ => mul_left_comm ..)
    _ = _ := turn.trans (Finset.sum_congr rfl fun t _ => congrArg (weight (C:=C) B e b t • ·)
      (congrArg (C.omega N p) (funext fun _ => mul_left_comm ..)))

end YM.Integration.WilsonFactoryPhysicalGlyphs
