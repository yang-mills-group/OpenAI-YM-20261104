import YM.SchemeConversionRG11.Read.Tensor
import YM.SchemeConversionRG11.Detector.Poll

/-!
# Boundary quantities

The same type of evaluated tensor can be supplied on many distinct constructions. These are
NOT prescription definitions. E.g. require `bareSide` data to be proved to supply the actual
WilsonX prescription before instantiation. Use real multilinear operator norms so that tests,
real coupling extraction, etc. are on scalar and field spaces with the same convention. The
adapter accepts an actual complex tensor and all readings in that case are literal evaluations
on those original complex fields.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11

open Function Filter Pert.Position Series Orbit Affine Horizon
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {r m d e : ℕ}

section Adapter

/-- This is just to use the operator-norm topology; no constant asserted uniform in field or
  perturbative demand. -/
def tapeOfReal (f : MultilinearMap ℝ (fun _ : Fin m ↦ E F d) ℂ) : Tape F d m ℂ := by
  classical
  refine ⟨f,?_⟩
  let B := Module.finBasis ℝ (E F d)
  have he (p : Fin m → E F d) : f p =
      ∑ z : (Fin m → Fin (Module.finrank ℝ (E F d))), (∏ j, B.coord (z j) (p j)) • f (fun j ↦ B (z j)) := by
    conv_lhs => rw [← funext fun j ↦ B.sum_equivFun (p j)]
    rw [MultilinearMap.map_sum_finset, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun _ _ ↦ MultilinearMap.map_smul_univ ..)
  change Continuous (fun p ↦ f p)
  conv => arg 1; ext p; rw [he p]
  -- prevent expanding f again
  exact continuous_finsetSum _ (fun v _ ↦ (continuous_finsetProd _ (fun j _ ↦
    (B.coord (v j)).continuous_of_finiteDimensional.comp (continuous_apply j))).smul continuous_const)

def tapeOfComplex (f : MultilinearMap ℂ (fun _ : Fin m ↦ E F d) ℂ) : Tape F d m ℂ :=
  tapeOfReal (F:=F) (f.restrictScalars ℝ)

theorem unchanged (f : MultilinearMap ℂ (fun _ : Fin m ↦ E F d) ℂ) (p : Fin m → E F d) :
    tapeOfComplex (F:=F) f p = f p := rfl
end Adapter

/-- Arrays of tensors tested linearly at fixed finite demand, one horizon (can e.g.
 be normalized hierarchy, formal output, finite bare). Include arity zero.
 Need normalization, locality, profile-linearity and coefficient prescription separately. -/
abbrev Issue (F : Labels.Frames G) (d : ℕ) := (m : ℕ) → (Test m) → Series (Tape F d m ℂ)

namespace Issue

/-- For this boundary, probe continuum/test functions as in the detector APIs. -/
def gaussian (F : Labels.Frames G) (d : ℕ) (t : Test m) := tapeOfComplex (F:=F) (wickReading F d t)

lemma gauss_at (p : Fin m → E F d) (t : Test m) : gaussian F d t p = wickReading F d t p :=
  unchanged (F:=F) _ _

lemma gauss_includes (t : Test m) (h : d ≤ e) : Tape.withinHorizon h (gaussian F e t) = gaussian F d t := by
  ext p
  rw [Tape.within_at, gauss_at, gauss_at]
  change t.applyTo _ = t.applyTo _
  exact congrArg t.applyTo (funext (fun x ↦ Detector.Poll.visibleIncl p x h))

/-- Finite perturbative array candidate: around the specific origin, at the period/top and
  quotient of Full.profile, not a continuum limit. Needs separate prescription adapter. -/
def bareSide (L : YM.Lattice.Side) (n : ℕ) : Issue F d := fun m t j ↦
  tapeOfComplex (F:=F) ((PowerSeries.coeff j).compMultilinearMap (Pert.Full.profile d m F L n t))

def imprint (X : Series (Buffer F d)) (A : Issue F d) : Issue F d := fun n t ↦ Tape.hinge X (A n t)

def insertSeries (x : Series ℝ) (A : Issue F d) : Issue F d := fun n t ↦ subJet (A n t) x

def Identifies (p : ℕ) (A B : Issue F d) := ∀ n t, Through p (A n t) (B n t)

/-- Does not assert regulator convergence outside the test domain. If varying positions or
  roots are needed, strengthen separately. -/
def Limits {α : Type*} (p : ℕ) (l : Filter α) (A : α → Issue F d) (M : Issue F d) :=
  ∀ n t, Converges p l (fun i ↦ A i n t) (M n t)

def Twist (A : Issue F d) := ∀ n (t : Test n), A n t 0 = gaussian F d t

/-- Compatibility between data of two horizons through finite order. -/
def Compatible (p : ℕ) (A : Issue F d) (B : Issue F e) (h : d ≤ e) :=
  ∀ m t, Through p (fun j ↦ Tape.withinHorizon h (B m t j)) (A m t)

lemma bare_compatible (p : ℕ) (L n) (h : d ≤ e) :
    Compatible (F:=F) p (bareSide L n) (bareSide L n) h := by
  intro m t i _
  apply ContinuousMultilinearMap.ext
  intro v
  rw [Tape.within_at]
  exact congrArg (PowerSeries.coeff (R:=ℂ) i) (Pert.Full.profile_coherent _ h (Maxwell.Free.scheme F)
    (Maxwell.Free.scheme_filters F) L n t v).symm

variable {A B : Issue F d} {C : Issue F e} {V : Series (Buffer F d)} {W : Series (Buffer F e)}

theorem aims (hv : A.Twist) (q : V 0 = 0) : Twist (imprint V A) := by
  intro m t
  unfold imprint Tape.hinge
  rw [liftJet_zero]; change Tape.put (V 0) _ = _; rw [q,Tape.put_zero]; exact hv ..

theorem Twist.series (ht : A.Twist) {x : Series ℝ} (hx : x 0 = 0) : Twist (insertSeries x A) :=
  fun _ _ ↦ (subJet_base hx).trans (ht ..)

theorem Compatible.moves (h : d ≤ e) (ht : Through r (fun i ↦ restr F h (W i)) V)
    (hc : Compatible r A C h) : Compatible r (imprint V A) (imprint W C) h := by
  intro m t
  let L := Tape.withinHorizon (m:=m) (F:=F) (W:=ℂ) h
  have hp := trunc_represents W r
  have hq := trunc_represents (C m t) r
  have hu := ((hp.linear (F:=Buffer F d) (restr F h)).congr ht)
  have hv := ((hq.linear (F:=Tape F d m ℂ) L).congr (hc m t))
  refine ((Tape.tape_jet hp hq).linear (F:=Tape F d m ℂ) L).unique ?_
  apply (Tape.tape_jet hu hv).germ
  exact Eventually.of_forall (fun z ↦ Tape.put_within h (trunc W r z) (trunc (C m t) r z))

theorem Compatible.bends (h : d ≤ e) {x : Series ℝ} (hx : x 0 = 0) (ht : Compatible r A C h) :
    Compatible r (insertSeries x A) (insertSeries x C) h := by
  intro m t
  let L := Tape.withinHorizon (m:=m) (F:=F) (W:=ℂ) h
  have hp := trunc_represents (C m t) r
  have hk := trunc_represents x r
  exact ((hp.subJet hk hx).linear (F:=Tape F d m ℂ) L).unique
    (((hp.linear (F:=Tape F d m ℂ) L).congr (ht m t)).subJet hk hx)

end Issue
end YM.SchemeConversionRG11
