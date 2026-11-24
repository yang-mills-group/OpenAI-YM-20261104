import YM.Integration.WilsonGraphCenteredFarReplacement
import YM.GradedFar.Continuation.Insert

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredBook

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

/-- The signed two-slot row uses the public inclusions at the common grade. -/
theorem filedAtPorts (h q : ℕ) (a b : Sec g.core h) (x y : YM.Points 1) (s t : ℝ)
    (hp : forest x (squeeze (-s) y) ∈ YM.conf (1+1)) :
    (∑ j ∈ Finset.range (q+1), (t : ℂ)^j * coeff j (Continuation.row (prescription g hg)
      (d := fun _ : Fin 1 => h) (e := fun _ : Fin 1 => h) x (fun _ => a) y (fun _ => b) s)) =
    publicTruncation (conversion.{u} g hg) (publicLetters (fun _ : Fin 2 => h) ![a,b])
      (forest x (squeeze (-s) y)) q t := by
  let w : Fin 2 → ℕ := fun _ => h
  let stage : Scale.Stage 2 := ⟨forest x (squeeze (-s) y), hp⟩
  have inlet : h ≤ publicDegree w := publicWithin w (0 : Fin 2)
  have slots : Fin.append
      (installedInputs (d := fun _ : Fin 1 => h) (fun _ => inlet) (fun _ => a))
      (installedInputs (d := fun _ : Fin 1 => h) (fun _ => inlet) (fun _ => b)) =
      toView w (publicDegree w) (publicWithin w) g.core ![a,b] := by
    funext i
    fin_cases i <;> rfl
  let Z := prescription g hg
  let Q := perspective.{u} g hg
  let E := WilsonGraphPaperPublication.construction.{u} g hg
  have paid : YM.Answer.ContinuumLimit.AllAppointedGraphSums E.paths Z Q.MS (Teller.logNu 1) :=
    (SourceOnlyGraphSum.originalAgreement (R := E.paths) Z Q.MS (Teller.logNu 1)).mpr
    (SourceOnlyGraphSum.atMatch Z Q.MS Q.matching (Teller.logNu 1))
  refine Eq.trans ?_ (publicMixedPolynomial (R := E.paths) Z Q.MS Q.matching paid w ![a,b] stage q t)
  unfold WilsonPositionHomogeneousComparison.polynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [WilsonPositionHomogeneousComparison.filed Z Q.MS Q.matching]
  apply congrArg (fun v : ℂ => (t : ℂ)^j * v)
  have port := Continuation.coeff_row (d := fun _ : Fin 1 => h) (e := fun _ : Fin 1 => h)
    Q.matching x (fun _ => a) y (fun _ => b) s (fun _ => inlet) (fun _ => inlet) hp j
  rwa [slots] at port

end YM.FVA2.GradedFar.AppointedCenteredBook
end

