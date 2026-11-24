import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedRiverFiling
import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedNumeratorViewerPrice
import YM.Integration.WilsonGraphAppointedNumeratorTranslation

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedTwoFiledPayments
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YangMills YM.Answer.ContinuumLimit YM.Integration Asymptotics
open scoped Topology BigOperators Classical ContDiff

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
variable {ι σ : Type*} [Fintype σ]
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev U := (V.{u} g hg periods strict).pupil.last
private abbrev frame := Elected.Hframe (N g hg) (U.{u} g hg periods strict) (V.{u} g hg periods strict).pupil.J
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)

/-- The filed numerator at the unselected viewer and origin zero pays the original continuum row. -/
theorem filingAtZero {n : ℕ} (d : Fin n → ℕ) (h p cap : ℕ)
    {X : Set (YM.Points n)} {Y : Set (YM.Points 1)}
    (hX : IsCompact X) (hx : X ⊆ conf n) (hY : IsCompact Y) (hy : Y ⊆ Outside 1)
    {C B : ℝ} (hC : 0<C) (hB : 0<B) (hd : ∀ i, d i ≤ cap) (he : ∀ _ : Fin 1, h ≤ cap)
    (river : Filter ι) (radius : ι → ℝ) (rowValue reportedCrop : σ → ι → ℂ)
    (fileHeat : σ → ι → ℝ) (title : σ → ι → PowerSeries ℂ)
    (filedPrice : ∀ s, (fun i => rowValue s i - reportedCrop s i) =O[river]
      (fun i => (meter g.core (radius i))^(p+1)))
    (sameHall : ∀ L R : ℝ, ∃ select : AppointedFiledMeter.Layout g.core d (fun _ : Fin 1 => h)
          (View (U.{u} g hg periods strict)) X Y L R → σ,
      ∃ arrive : AppointedFiledMeter.Layout g.core d (fun _ : Fin 1 => h)
          (View (U.{u} g hg periods strict)) X Y L R → ι,
        Tendsto arrive (Filter.comap AppointedFiledMeter.Layout.w (windows (upper g.core C B))) river ∧
        ∀ᶠ l in Filter.comap AppointedFiledMeter.Layout.w (windows (upper g.core C B)),
          radius (arrive l) = l.w.len ∧
          rowValue (select l) (arrive l) =
            Physical.Y0 (U.{u} g hg periods strict) (frame.{u} g hg periods strict)
              d (fun _ : Fin 1 => h) l.w (none,0) l.x l.y l.u l.v ∧
          fileHeat (select l) (arrive l) = heat.{u} g hg periods strict l.w.len ∧
          reportedCrop (select l) (arrive l) =
            crop p (fileHeat (select l) (arrive l)) (title (select l) (arrive l)) ∧
          ∃ safe : forest l.x (squeeze (-l.w.sep) l.y) ∈ conf (n+1),
            ∀ j ≤ p, coeff j (title (select l) (arrive l)) =
              Measure.outlook (N g hg).scheme (N g hg).criterion cap _
                ⟨forest l.x (squeeze (-l.w.sep) l.y),safe⟩ j
                (Fin.append (installedInputs hd l.u) (installedInputs he l.v))) :
    Filing (N g hg) (U.{u} g hg periods strict) (frame.{u} g hg periods strict)
      d (fun _ : Fin 1 => h) X Y (upper g.core C B) (heat.{u} g hg periods strict) p := by
  classical
  choose cost positive budget using fun s => (filedPrice s).exists_pos
  let D : ℝ := 1 + ∑ s, cost s
  have sumPositive : 0 ≤ ∑ s, cost s := Finset.sum_nonneg fun s _ => (positive s).le
  have hD : 0<D := by dsimp [D]; linarith
  have rates : ∀ᶠ i in river, ∀ s, ‖rowValue s i - reportedCrop s i‖ ≤
      cost s * ‖(meter g.core (radius i))^(p+1)‖ := eventually_all.mpr fun s => (budget s).bound
  refine ⟨cap,hd,he,?_⟩
  intro L R
  obtain ⟨select,arrive,reaches,incidence⟩ := sameHall L R
  obtain ⟨phaseCost,phasePositive,viewers⟩ := AppointedNumeratorViewer.onWindow.{u}
    g hg periods strict d h p hX hx hY hy L R hC hB
  let window := @AppointedFiledMeter.Layout.w g.core n 1 d (fun _ : Fin 1 => h)
    (View (U.{u} g hg periods strict)) X Y L R
  have lift : Tendsto window (Filter.comap window (windows (upper g.core C B))) (windows (upper g.core C B)) :=
    tendsto_comap
  let read := fun l : AppointedFiledMeter.Layout g.core d (fun _ : Fin 1 => h)
      (View (U.{u} g hg periods strict)) X Y L R =>
    Physical.Y0 (U.{u} g hg periods strict) (frame.{u} g hg periods strict)
      d (fun _ : Fin 1 => h) l.w l.viewer l.x l.y l.u l.v
  refine ⟨read,fun l => title (select l) (arrive l),fun l => fileHeat (select l) (arrive l),
    phaseCost+D,add_pos phasePositive hD,0,?_⟩
  filter_upwards [incidence,reaches.eventually rates,lift.eventually viewers,
    lift.eventually ((windows_short _).eventually self_mem_nhdsWithin)]
    with l same filed moved (short : 0 < l.w.len)
  obtain ⟨radiusAt,original,heatAt,cropAt,safe,coeffs⟩ := same
  refine ⟨rfl,heatAt,⟨safe,coeffs⟩,?_⟩
  have translation := AppointedNumeratorTranslation.onPlacement
    (U.{u} g hg periods strict) (frame.{u} g hg periods strict) l.w short none l.viewer.2 l.x l.y l.u l.v safe
  have changeViewer := moved l.viewer l.x l.hx l.y l.hy l.u l.hu l.v l.hv
  rw [translation,← original] at changeViewer
  have nonneg : 0 ≤ (meter g.core l.w.len)^(p+1) := by unfold meter; positivity
  have each : cost (select l) ≤ D := by
    have hs := Finset.single_le_sum (s := Finset.univ) (f := cost)
      (fun s _ => (positive s).le) (Finset.mem_univ (select l))
    dsimp [D]; linarith
  have paid := filed (select l)
  rw [radiusAt,Real.norm_eq_abs,abs_of_nonneg nonneg] at paid
  simp only [pow_zero,mul_one]
  rw [← cropAt]
  calc
    ‖read l - reportedCrop (select l) (arrive l)‖ =
        ‖(read l - rowValue (select l) (arrive l)) +
          (rowValue (select l) (arrive l) - reportedCrop (select l) (arrive l))‖ := by
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ phaseCost*(meter g.core l.w.len)^(p+1) + D*(meter g.core l.w.len)^(p+1) :=
      add_le_add changeViewer (paid.trans (mul_le_mul_of_nonneg_right each nonneg))
    _ = (phaseCost+D)*(meter g.core l.w.len)^(p+1) := (add_mul ..).symm

end YM.FVA2.GradedFar.AppointedTwoFiledPayments
end

