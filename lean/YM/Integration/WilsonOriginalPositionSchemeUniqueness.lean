import YM.Integration.WilsonPositionThermometerRunning
import YM.FVA2.Main

/-! Uniqueness of the MS change from all orders of the smeared Wilson readings
on one continuum extraction. Every comparison evaluates a finite polynomial
at that extraction's signed three-field thermometer. -/
set_option autoImplicit false
set_option format.width 160
noncomputable section
namespace YM.Integration.WilsonOriginalPositionSchemeUniqueness

open Filter Finset Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open scoped Topology BigOperators Classical

private def priced (t : ℝ → ℝ) (x : ℝ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ k ε, 0 < ε → ∀ᶠ r in trail,
    ‖x r - ∑ j ∈ range (k+1), (t r : ℂ)^j*a j‖ ≤ ε*|t r|^k

private theorem determines {t : ℝ → ℝ} {x : ℝ → ℂ} {a b : ℕ → ℂ}
    (pos : ∀ᶠ r in trail, 0 < t r) (ha : priced t x a) (hb : priced t x b) : a = b := by
  funext k
  induction k using Nat.strong_induction_on with
  | h k earlier =>
    by_contra different
    have gap : 0 < ‖a k - b k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr different)
    let ε := ‖a k - b k‖/4
    have hp : 0 < ε := div_pos gap (by norm_num)
    obtain ⟨r, ht, h1, h2⟩ := (pos.and ((ha k ε hp).and (hb k ε hp))).exists
    have lower : (∑ j ∈ range k, (t r : ℂ)^j*a j) = ∑ j ∈ range k, (t r : ℂ)^j*b j :=
      sum_congr rfl fun j hj => by rw [earlier j (mem_range.mp hj)]
    have split : (∑ j ∈ range (k+1), (t r : ℂ)^j*a j) -
        (∑ j ∈ range (k+1), (t r : ℂ)^j*b j) = (t r : ℂ)^k*(a k-b k) := by
      rw [sum_range_succ, sum_range_succ, lower]
      ring
    have paid := norm_sub_le_norm_sub_add_norm_sub
      (∑ j ∈ range (k+1), (t r : ℂ)^j*a j) (x r) (∑ j ∈ range (k+1), (t r : ℂ)^j*b j)
    rw [split, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      norm_sub_rev _ (x r)] at paid
    have bound : ‖a k-b k‖ * |t r|^k ≤ (ε+ε) * |t r|^k := by
      rw [mul_comm, add_mul]
      exact paid.trans (add_le_add h1 h2)
    have small := le_of_mul_le_mul_right bound (pow_pos (abs_pos.mpr ht.ne') _)
    dsimp [ε] at small
    linarith

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ → PhysMS.tower S)

/-- The same physical smeared ordinary product and the same fields are used
at every order. One vacuum suffices to identify its formal coefficients. -/
def heard (t : ℝ → ℝ) (A : Arenas G) : Prop :=
  ∀ d n (φ : Test n) (v : Fin n → Sec G d), priced t
    (fun r => φ.applyTo (PhysMS.measured F none (J r) (d := fun _ => d)
      (fun i => (Maxwell.Free.fields R.family.labels d).symm (v i)) r))
    (fun k => φ.applyTo (fun x => Jury.fxt (A d) x k v))

variable (Z : WilsonPrescription G) {hG : G.Simple}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {σ : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T σ dial)
  (Jθ : ℝ → PhysMS.tower S)
local notation "θ" => WilsonPositionThermometerReading.reading F Jθ Z.criterion

include M in
/-- Compact separated test data on the original extraction determines every
coefficient, hence the unique real coupling and the entire compatible field
tower. The same change acts on the independently prescribed OPE output. -/
theorem original (ν : ℝ) (physical : Coupling G θ)
    (issued : heard F J θ (Measure.outlook Z.scheme Z.criterion)) :
    (∃! pair : PowerSeries ℂ × Frames G, Tangent pair.1 ∧
      (∀ d, Base (pair.2 d)) ∧ heard F J θ (fun d =>
        Facets.actMark (pair.2 d) (Facets.couple pair.1 (Equator.wave ν T d)))) ∧
    (∀ a b (h : a ≤ b), Walk h (Measure.Z Z.scheme Z.criterion ν T a)
      (Measure.Z Z.scheme Z.criterion ν T b)) ∧ O.Canon.Supplied Z T ν := by
  refine ⟨?_, M.frameCompat ν, M.separatedOPE ν⟩
  refine ⟨⟨Measure.f Z.criterion ν T, Measure.Z Z.scheme Z.criterion ν T⟩,
    ⟨(M.positionCoupling ν).1, fun d => (M.frame ν d).1, ?_⟩, ?_⟩
  · exact (funext (M.eqconv ν)).symm ▸ issued
  · rintro ⟨p,W⟩ ⟨hp,hW,actual⟩
    obtain ⟨scalar,fields⟩ := M.uniqueConversion ν p W hp hW (fun d => by
      let P := Facets.actMark (W d) (Facets.couple p (Equator.wave ν T d))
      let A := Measure.outlook Z.scheme Z.criterion d
      have sourced := (Jury.initial (d := d) ν T).light
      have Pcont : Jury.Thin P := (sourced.glance p).specify (W d)
      have Acont : Jury.Thin A := by
        dsimp only [A]
        rw [← M.eqconv ν d]
        exact (sourced.glance (Measure.f Z.criterion ν T)).specify (Measure.Z Z.scheme Z.criterion ν T d)
      change P = A
      funext n x k
      ext1 v
      have uniform : ∀ φ : Test n,
          φ.applyTo (fun y => Jury.fxt P y k v) = φ.applyTo (fun y => Jury.fxt A y k v) :=
        fun φ => congrFun (determines physical.positive (actual d n φ v) (issued d n φ v)) k
      have equal := (Test.unique_kernel (Pcont n k v) (Acont n k v)).mp uniform x.property
      simpa only [Jury.exactC] using equal)
    exact Prod.ext scalar fields

end YM.Integration.WilsonOriginalPositionSchemeUniqueness
