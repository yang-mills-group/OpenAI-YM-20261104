import YM.Integration.WilsonEpochCalibratedInsertion
import YangMills.WilsonProof.NativeSupport.YM.MS.Bare.Shadows

/-! The precise open Bolt input for every primitive of the independently
booked Wick source, at its prescribed position on the physical torus.
All components and wrapped edges of the exponential coordinate chart are
retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochOpenSource

open Function Filter Lattice Source Source.Drops Labels Wilson PhysicalNext.Repeat.Legato
open FormalBulk08 FormalBulk08.Reef FormalBulk08.Flat FormalBulk08.Wick
open FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Lava FormalBulk08.Kemp
open FormalBulk08.Pose FormalBulk08.Dawn FormalBulk08.Rial FormalBulk08.Roof
open Planned.PrimaryIntegral295 Place Film Carrier PowerSeries
open RG Precision Next.Free Stationary Lotus Shore Mesa Gorge City Cork Rift Glide Bank Wine Dove Bloch
open FormalBulk08.Orb Work.F03 Work.F05 Work.F08
open FVA2 FVA2.Arrival FVA2.Register
open scoped ContDiff Topology Classical BigOperators
variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)
variable {d D : ℕ}

/-- The normalized physical Jacobians on their common actual chart germ. -/
theorem haar (N : WilsonPrescription G) :
    R.metals.O.J =ᶠ[𝓝 0] N.chart.J :=
  (MS.Bare.Maurer.real_ratio R.metals.oga).trans
    (MS.Bare.Maurer.real_ratio N.analyticChart).symm

private def levelZero (d : ℕ) : Dawn.Spring d :=
  ⟨0,(Dawn.paper_is _).mpr (by simp [Chapel.upper])⟩

def letter (F : Frame G d) (j : F.Index) : Letter F :=
  ⟨(j,levelZero d),Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
    simpa [levelZero,Chapel.upper] using F.bound j⟩⟩

variable (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G) (depth : d < D)
def leaf (N per : ℕ) (p : Cover) (j : (R.family.labels.level d).Index) :
    Pap (wire G (R.family.side N per)) :=
  let F := R.family.labels.level d
  let n := R.family.side N per
  Kemp.resite (wrap n p) (X^(F.grades j).2 *
    Kemp.banner d (WilsonRunFormalMarkedStep.graph R L a depth N N (letter F j) (Dawn.cone D 0)) n)

private theorem reroot {F : Frame G d} (T : SectionData F) (j : F.Index)
    (n : Side) (p : Site n) :
    ContDiffAt ℝ ∞ (fun z : Jets.Rays (wire G n) => (T.places (copy F j) p (input G n z)).re) 0 ∧
    Kemp.resite p (paste (fun z : Jets.Rays (wire G n) => (T.places (copy F j) 0 (input G n z)).re)) =
      paste (fun z : Jets.Rays (wire G n) => (T.places (copy F j) p (input G n z)).re) := by
  let f := fun z : Jets.Rays (wire G n) => (T.places (copy F j) 0 (input G n z)).re
  let pull := fun z : Jets.Rays (wire G n) => z ∘ Lotus.tint p
  have smooth : ContDiffAt ℝ ∞ pull 0 := contDiffAt_pi.mpr fun i => contDiffAt_apply ..
  have hz : pull 0 = 0 := rfl
  have h (z : Jets.Rays (wire G n)) : f (pull z) = (T.places (copy F j) p (input G n z)).re := by
    change (T.places (copy F j) 0 (Lattice.translate p (input G n z))).re = _
    rw [T.places_trans,zero_add]
  have e := funext h
  have hf : ContDiffAt ℝ ∞ f 0 := Rial.coatG T n j
  constructor
  · rw [←e]
    exact (show ContDiffAt ℝ ∞ f (pull 0) from hz ▸ hf).comp 0 smooth
  · rw [←e]
    exact (fit_translate (Lotus.tint p) (paste f)).symm.trans
      (paste_steps f pull hf smooth hz).symm

/-- Recovers the literal physical gauge basis including its independent
translation and its complete Laurent restoration at the actual UV boundary. -/
theorem selected (N per : ℕ) (p : Cover) (j : (R.family.labels.level d).Index) :
    let F := R.family.labels.level d
    let n := R.family.side N per
    leaf R L a depth N per p j =
      paste (fun z : Jets.Rays (wire G n) =>
        ((R.family.localSection d).places (copy F j) (wrap n p) (input G n z)).re) := by
  intro F n
  have init := WilsonBookedSectionGerm.ultraviolet R L a depth N per (letter F j)
    (Dawn.cone D 0) d (Film.second_fits F j)
  let f := fun z : Jets.Rays (wire G n) => ((R.family.localSection d).places
      (copy F j) 0 (input G n z)).re
  have unit : X^(F.grades j).2 *
      Kemp.banner d (WilsonRunFormalMarkedStep.graph R L a depth N N (letter F j) (Dawn.cone D 0)) n =
      paste f := init.trans (by
    change PowerSeries.C (MvPolynomial.C (Dawn.notch 0 _ (Dawn.cone D 0))) * paste f = _
    simp [Dawn.notch_basis])
  exact (congrArg (Kemp.resite (wrap n p)) unit).trans
    (reroot (R.family.localSection d) j n (wrap n p)).2

/-- All components of a booked, possibly subtracted Wick input come out of
the genuine physical open graph. No zero-position or scalar-basis selection
is made on the right-hand side. -/
theorem original (Y : XSpace.Initialize G) (s : Folio G) (h : s.u.size < D) (N per : ℕ) :
    let F := R.family.labels.level s.u.size
    let n := R.family.side N per
    ∑ j : F.Index, PowerSeries.C (MvPolynomial.C ((F.coords (s.item Y) j).re)) *
        leaf R L a h N per s.addr j =
      paste (fun z : Jets.Rays (wire G n) => WilsonEpochPositionCoefficients.placed
        R Y n s (input G n z)) := by
  intro F n
  let T := R.family.localSection s.u.size
  let o := wrap n s.addr
  let c := F.coords (s.item Y)
  let v := fun j : F.Index => fun z : Jets.Rays (wire G n) => (T.places (copy F j) o (input G n z)).re
  have hv (j : F.Index) : ContDiffAt ℝ ∞ (v j) 0 := (reroot T j n o).1
  have he : (fun z : Jets.Rays (wire G n) => WilsonEpochPositionCoefficients.placed R Y n s (input G n z)) =
      ∑ j : F.Index, (c j).re • v j := by
    funext z
    have eq := congrArg Complex.re (ActualStencilCylinder.section_expansion T (R.makes.sections _) c n o (input G n z))
    simpa only [WilsonEpochPositionCoefficients.placed,ActualStencilCylinder.observed,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Complex.re_sum,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,v,copy] using eq
  rw [he,Jets.garter (fun j => (c j).re • v j) Finset.univ (fun j _ => (hv j).const_smul (c j).re)]
  apply Finset.sum_congr rfl
  intro j _
  rw [selected R L a h N per s.addr j]
  exact Rial.scalar_paste (c j).re (v j) (hv j)

end YM.Integration.WilsonEpochOpenSource
end

