import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedTwoFiledPayments

namespace YM.FVA2.GradedFar.AppointedTwoFiledPayments
noncomputable section
set_option maxHeartbeats 4000000
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical ContDiff

open Asymptotics

variable {G : Gauge} {n m : ℕ} {A : Family G} {o : Extraction.Order} {P : Table A.book}
variable {ι σ : Type*} [Fintype σ]

theorem filingFromFiniteRiver
    (N : Register.WilsonPrescription G) (U : Spec.Final A o P) (H : FramesH P)
    (d : Fin n → ℕ) (e : Fin m → ℕ) (K : Set (Points n)) (S : Set (Points m))
    (W : Set Window) (t : ℝ → ℝ) (p cap : ℕ) (hd : ∀ i, d i ≤ cap) (he : ∀ i, e i ≤ cap)
    (river : Filter ι) (radius : ι → ℝ) (rowValue reportedCrop : σ → ι → ℂ)
    (fileHeat : σ → ι → ℝ) (title : σ → ι → PowerSeries ℂ)
    (filedPrice : ∀ s, (fun i => rowValue s i - reportedCrop s i) =O[river]
      (fun i => (meter G (radius i))^(p+1)))
    (sameHall : ∀ L R : ℝ, ∃ select : AppointedFiledMeter.Layout G d e (View U) K S L R → σ,
      ∃ arrive : AppointedFiledMeter.Layout G d e (View U) K S L R → ι,
        Tendsto arrive (Filter.comap AppointedFiledMeter.Layout.w (windows W)) river ∧
        ∀ᶠ l in Filter.comap AppointedFiledMeter.Layout.w (windows W),
          radius (arrive l) = l.w.len ∧
          rowValue (select l) (arrive l) = Physical.Y0 U H d e l.w l.viewer l.x l.y l.u l.v ∧
          fileHeat (select l) (arrive l) = t l.w.len ∧
          reportedCrop (select l) (arrive l) =
            crop p (fileHeat (select l) (arrive l)) (title (select l) (arrive l)) ∧
          ∃ hc : forest l.x (squeeze (-l.w.sep) l.y) ∈ conf (n+m),
            ∀ j ≤ p, coeff j (title (select l) (arrive l)) =
              Measure.outlook N.scheme N.criterion cap _ ⟨forest l.x (squeeze (-l.w.sep) l.y),hc⟩ j
                (Fin.append (installedInputs hd l.u) (installedInputs he l.v))) :
    Filing N U H d e K S W t p := by
  classical
  choose C hC budget using fun s => (filedPrice s).exists_pos
  let D : ℝ := 1 + ∑ s, C s
  have hsum : 0 ≤ ∑ s, C s := Finset.sum_nonneg fun s _ => (hC s).le
  have hD : 0 < D := by dsimp [D]; linarith
  have rates : ∀ᶠ i in river, ∀ s, ‖rowValue s i - reportedCrop s i‖ ≤
      C s * ‖(meter G (radius i))^(p+1)‖ :=
    eventually_all.mpr fun s => (budget s).bound
  refine ⟨cap,hd,he,?_⟩
  intro L R
  obtain ⟨select,arrive,reaches,incidence⟩ := sameHall L R
  refine ⟨fun l => rowValue (select l) (arrive l), fun l => title (select l) (arrive l),
    fun l => fileHeat (select l) (arrive l),D,hD,0,?_⟩
  filter_upwards [incidence,reaches.eventually rates] with l inc paid
  obtain ⟨hr,hy,ht,hcrop,coeffs⟩ := inc
  refine ⟨hy,ht,coeffs,?_⟩
  have each : C (select l) ≤ D := by
    have h := Finset.single_le_sum (s := Finset.univ) (f := C)
      (fun s _ => (hC s).le) (Finset.mem_univ (select l))
    dsimp [D]; linarith
  have nonneg : 0 ≤ meter G l.w.len := by unfold meter; positivity
  have bound := paid (select l)
  rw [hr, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg nonneg _), hcrop] at bound
  simpa only [pow_zero,mul_one] using
    bound.trans (mul_le_mul_of_nonneg_right each (pow_nonneg nonneg _))

end
end YM.FVA2.GradedFar.AppointedTwoFiledPayments

