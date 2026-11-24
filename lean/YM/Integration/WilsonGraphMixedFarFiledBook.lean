import YM.Integration.WilsonGraphCenteredFarFiledBook

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedMixedBook

open YangMills PowerSeries YM.Answer.ContinuumLimit YM.Integration
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe YM.Integration.Election.Frames
open scoped BigOperators

universe u
variable (g : GaugeGroup) (hg : g.IsSimple)
private abbrev prescription := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev perspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev conversion := _root_.IssuedBridge.PostedAppointedConversion.filed
  (prescription g hg) (perspective.{u} g hg).MS (perspective.{u} g hg).matching (YM.FVA2.Teller.logNu 1)

/-- The appointed row uses each near and far slot at its own public grade. -/
theorem filedAtPorts {n m : ℕ} (w : Fin (n+m) → ℕ)
    (a : (i : Fin (n+m)) → Sec g.core (w i)) (x : YM.Points n) (y : YM.Points m)
    (q : ℕ) (s t : ℝ) (hp : forest x (squeeze (-s) y) ∈ YM.conf (n+m)) :
    (∑ j ∈ Finset.range (q+1), (t : ℂ)^j * coeff j (Continuation.row (prescription g hg)
      (d := fun i : Fin n => w (Fin.castAdd m i)) (e := fun i : Fin m => w (Fin.natAdd n i))
      x (fun i => a (Fin.castAdd m i)) y (fun i => a (Fin.natAdd n i)) s)) =
    publicTruncation (conversion.{u} g hg) (publicLetters w a)
      (forest x (squeeze (-s) y)) q t := by
  let stage : Scale.Stage (n+m) := ⟨forest x (squeeze (-s) y), hp⟩
  have slots : Fin.append
      (installedInputs (d := fun i : Fin n => w (Fin.castAdd m i))
        (fun i => publicWithin w (Fin.castAdd m i)) (fun i => a (Fin.castAdd m i)))
      (installedInputs (d := fun i : Fin m => w (Fin.natAdd n i))
        (fun i => publicWithin w (Fin.natAdd n i)) (fun i => a (Fin.natAdd n i))) =
      toView w (publicDegree w) (publicWithin w) g.core a := by
    funext i
    induction i using Fin.addCases <;> simp [Fin.append] <;> rfl
  let Z := prescription g hg
  let Q := perspective.{u} g hg
  let E := WilsonGraphPaperPublication.construction.{u} g hg
  have paid : YM.Answer.ContinuumLimit.AllAppointedGraphSums E.paths Z Q.MS (Teller.logNu 1) :=
    (SourceOnlyGraphSum.originalAgreement (R := E.paths) Z Q.MS (Teller.logNu 1)).mpr
      (SourceOnlyGraphSum.atMatch Z Q.MS Q.matching (Teller.logNu 1))
  refine Eq.trans ?_ (publicMixedPolynomial (R := E.paths) Z Q.MS Q.matching paid w a stage q t)
  unfold WilsonPositionHomogeneousComparison.polynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [WilsonPositionHomogeneousComparison.filed Z Q.MS Q.matching]
  apply congrArg (fun v : ℂ => (t : ℂ)^j * v)
  have port := Continuation.coeff_row
    (d := fun i : Fin n => w (Fin.castAdd m i)) (e := fun i : Fin m => w (Fin.natAdd n i))
    Q.matching x (fun i => a (Fin.castAdd m i)) y (fun i => a (Fin.natAdd n i)) s
    (fun i => publicWithin w (Fin.castAdd m i)) (fun i => publicWithin w (Fin.natAdd n i)) hp j
  rwa [slots] at port

end YM.FVA2.GradedFar.AppointedMixedBook
end

