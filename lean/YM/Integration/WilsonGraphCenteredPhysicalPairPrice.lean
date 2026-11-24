import YM.Integration.WilsonGraphCenteredPhysicalNames

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredPhysicalNames

open Filter Real Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YM.Answer.ContinuumLimit YM.Integration
open WilsonGraphCenteredFarReplacement (atFar)
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev H := Elected.Hframe (Z g hg) (V.{u} g hg periods strict).pupil.last
  (V.{u} g hg periods strict).pupil.J
private abbrev publicTable := YangMills.hierarchy (g := g) (V.{u} g hg periods strict).pupil.last
  (V.{u} g hg periods strict).pupil.P
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (Z g hg)

/-- The two original physical continuum readings share one compact estimate. The
far heater evaluates both crops. In the mixed reading only the center is rebased. -/
theorem pairedOnWindow (h q : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (separated : K ⊆ YM.conf 2) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ e : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C * (gYM g.core r)^(-B) →
      ∀ (a b : Sec g.core h) (phase : Option (publicTable.{u} g hg periods strict).Character)
        (o : Spacetime) (y : YM.Points 1), (WithLp.toLp 2 ![0,y 0] : YangMills.Points 2) ∈ K →
        let w : Window := (r,s)
        let f := r * exp s
        let la := atFar.{u} g hg periods strict h r f a
        let lb := atFar.{u} g hg periods strict h r f b
        let expense := D * (‖chair g.core h a‖ * ‖chair g.core h b‖) * (gYM g.core r)^(q+1) * (1+s)^e
        ‖Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
            (fun _ : Fin 1 => h) (fun _ : Fin 1 => h) w (phase,o) (0 : YM.Points 1) y
            (fun _ => a) (fun _ => b) -
          crop q (heat.{u} g hg periods strict f) (AppointedCenteredRows.series g hg h la lb (y 0))‖ ≤ expense ∧
        ‖Physical.Dactual (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
            r f (phase,o) y (e := fun _ : Fin 1 => h) (fun _ => b) a -
          crop q (heat.{u} g hg periods strict f) (AppointedCenteredRows.series g hg h la b (y 0))‖ ≤ expense := by
  obtain ⟨D,hD,e,prices⟩ := AppointedCenteredPhysicalPrice.onWindow.{u}
    g hg periods strict h q K compact separated hC hB
  refine ⟨D,hD,e,?_⟩
  have positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  filter_upwards [prices,positive] with r bill hr
  intro s hs upper a b phase o y hK
  let w : Window := (r,s)
  have near := allNear.{u} g hg periods strict h w hr a b phase o y (separated hK)
  have far := mixed.{u} g hg periods strict h w hr a b phase o y (separated hK)
  let f := r * exp s
  let la := atFar.{u} g hg periods strict h r f a
  let lb := atFar.{u} g hg periods strict h r f b
  let nearCrop := crop q (heat.{u} g hg periods strict f) (AppointedCenteredRows.series g hg h la lb (y 0))
  let farCrop := crop q (heat.{u} g hg periods strict f) (AppointedCenteredRows.series g hg h la b (y 0))
  have paid := bill s hs upper a b phase o (y 0) hK
  exact ⟨(congrArg (fun z : ℂ => ‖z - nearCrop‖) near).symm.le.trans paid.1,
    (congrArg (fun z : ℂ => ‖z - farCrop‖) far).symm.le.trans paid.2⟩

end YM.FVA2.GradedFar.AppointedCenteredPhysicalNames

