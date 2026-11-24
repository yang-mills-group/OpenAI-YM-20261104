import YM.Integration.WilsonGraphCenteredFarFiledBook

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredRows

open Filter YangMills YangMills.Matching PowerSeries YM.Answer.ContinuumLimit YM.Integration
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus O.Score O.Enh
open WilsonGraphPublishedShapeEstimate WilsonGraphPreElectedShapeEstimates
open WilsonGraphCenteredFarReplacement (atFar PairPrice)
open scoped Topology BigOperators

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev prescription := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev perspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev pick := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)
private abbrev hierarchy := YangMills.hierarchy (g := g) (pick.{u} g hg periods strict).pupil.last
  (pick.{u} g hg periods strict).pupil.P
private abbrev conversion := _root_.IssuedBridge.PostedAppointedConversion.filed
  (prescription g hg) (perspective.{u} g hg).MS (perspective.{u} g hg).matching (YM.FVA2.Teller.logNu 1)

private def farPoint (y : Spacetime) : YM.Points 1 := WithLp.toLp 2 (fun _ => y)

private theorem positions (y : Spacetime) :
    forest (0 : YM.Points 1) (squeeze (-(0:ℝ)) (farPoint y)) = WithLp.toLp 2 ![0,y] := by
  simp only [squeeze, neg_zero, Real.exp_zero, one_smul]
  apply congrArg (WithLp.toLp 2)
  funext i
  fin_cases i <;> rfl

/-- The signed #309 row at the center and the far point in units of f. -/
def series (h : ℕ) (a b : Sec g.core h) (y : Spacetime) : PowerSeries ℂ :=
  Continuation.row (prescription g hg) (d := fun _ : Fin 1 => h) (e := fun _ : Fin 1 => h)
    (0 : YM.Points 1) (fun _ => a) (farPoint y) (fun _ => b) 0

theorem centeredCrop (h q : ℕ) (a b : Sec g.core h) (y : Spacetime) (t : ℝ)
    (separated : WithLp.toLp 2 ![0,y] ∈ YM.conf 2) :
    crop q t (series g hg h a b y) =
      ∑ k : Fin (q+1), (t : ℂ)^k.val * WilsonGraphStandaloneCorrelation.converted
        (conversion.{u} g hg) k.val (publicLetters (fun _ : Fin 2 => h) ![a,b]) (WithLp.toLp 2 ![0,y]) := by
  have hp : forest (0 : YM.Points 1) (squeeze (-(0:ℝ)) (farPoint y)) ∈ YM.conf 2 := by
    rwa [positions]
  have paid := AppointedCenteredBook.filedAtPorts.{u} g hg h q a b 0 (farPoint y) 0 t hp
  rw [positions] at paid
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (t : ℂ)^k *
    WilsonGraphStandaloneCorrelation.converted (conversion.{u} g hg) k
      (publicLetters (fun _ : Fin 2 => h) ![a,b]) (WithLp.toLp 2 ![0,y]))]
  rw [YM.FVA2.GradedFar.crop_eq]
  exact paid

/-- The compact estimate and the filed independent value on the same physical pair. -/
def FiledPair (h q : ℕ) (A r s f : ℝ) (a b center far : Sec g.core h)
    (phase : Option (hierarchy.{u} g hg periods strict).Character) (o y : Spacetime) : Prop :=
  let x : YangMills.Points 2 := WithLp.toLp 2 ![0,y]
  let t := ElectedMeasurement.clock (pick.{u} g hg periods strict) (prescription g hg) f
  PairPrice.{u} g hg periods strict h q A r s f a b ![center,far] phase o x ∧
    crop q t (series g hg h center far y) =
      ∑ k : Fin (q+1), (t : ℂ)^k.val * WilsonGraphStandaloneCorrelation.converted
        (conversion.{u} g hg) k.val (publicLetters (fun _ : Fin 2 => h) ![center,far]) x

theorem enteredOnPick (h q : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (separated : K ⊆ YM.conf 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ f : ℝ in 𝓝[>] 0, ∀ (r : ℝ) (a b : Sec g.core h)
      (phase : Option (hierarchy.{u} g hg periods strict).Character) (o y : Spacetime),
      let x : YangMills.Points 2 := WithLp.toLp 2 ![0,y]
      x ∈ K →
        FiledPair.{u} g hg periods strict h q A r r f a b
          (atFar.{u} g hg periods strict h r f a) (atFar.{u} g hg periods strict h r f b) phase o y ∧
        FiledPair.{u} g hg periods strict h q A r f f a b
          (atFar.{u} g hg periods strict h r f a) b phase o y := by
  obtain ⟨A,hA,late⟩ := WilsonGraphCenteredFarReplacement.centered.{u}
    g hg periods strict h q K compact separated
  refine ⟨A,hA,?_⟩
  filter_upwards [late] with f hf
  intro r a b phase o y x hx
  obtain ⟨allNear,mixed⟩ := hf r a b phase o y hx
  exact ⟨⟨allNear, centeredCrop.{u} g hg h q _ _ y _ (separated hx)⟩,
    ⟨mixed, centeredCrop.{u} g hg h q _ _ y _ (separated hx)⟩⟩

end YM.FVA2.GradedFar.AppointedCenteredRows
end

