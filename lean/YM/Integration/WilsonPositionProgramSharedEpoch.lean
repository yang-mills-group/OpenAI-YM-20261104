import YM.Integration.WilsonPositionProgramArithmeticRegistered
import YM.Integration.WilsonPositionProgramSharedInversionTariff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramSharedEpoch
open WilsonPositionProgramInversionMaterial WilsonPositionProgramSeriesRead
open Filter Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open WilsonThermometerPositionInversionWords WilsonPositionProgramSignedFace
open WilsonPositionProgramReporterBand
open XSpace XSpace.Cirrus FVA2 FVA2.Register MS MS.Land
open scoped Classical ENNReal BigOperators
variable {G : Gauge} (C : Run G) {AUX : Type}
    {simple : G.Simple} {a : Axis} {ε : ℝ}
    (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (branch : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
    (Z : WilsonPrescription G) {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (matchMS : Main.Match Z simple M T dial)
local notation "Ω₀" => ℕ × AUX
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
local notation "Λ" => RG16.Lambda C.family.path.levels

include first paid slow matchMS in
/-- The original Wilson film, the whole normalized inversion and the
 calibrated position correction are evaluated on one enrolled circuit. -/
theorem original (Q : Prescription (Press.portDeck G))
    (calibration : TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR C) (Press.portDeck G)) Q)
    (floor : ℕ) {d₀ : ℕ} (hd : 0<d₀) (ratio : Z.run.ratio=(3:ℕ)^d₀)
    (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m))
    {n : ℕ} (nonempty : 0<n) (K : Set (Points n)) (compact : IsCompact K) (apart : K⊆conf n) :
    ∃ stage, ∃ B : Band C Z.run stage, (∀ t, floor ≤ B.index t) ∧
      let m := fun u : Ω₀ => B.lower u.1
      let j := fun u : Ω₀ => B.span u.1
      let w := fun u : Ω₀ => B.powers u.1
      let S := WilsonPositionProgramInfraredCircuit.circuit C Z.run m j w (fun u => B.blocks u.1)
      ∀ (z : Ω₀ → Fin n → Cover) (c : Ω₀ → Four ℝ),
      (∀ u, c u ∈ (Z.run.step (B.index u.1)).Box) → (∀ u, (Z.run.step (B.index u.1)).rel (z u) (c u) ∈ K) →
      ∃ F : Tent j, Notebook S Y G branch color (Rocket.native j) F p ∧
        (∀ (I : Type) [Fintype I] [LinearOrder I] (child : I → Fin n)
          (d : I → ℕ) (T₀ : ∀ t, (Z.run.step (B.index t)).p.Tree) (q : ℕ), q ≤ p →
        ∀ strength : ℕ, ∀ᶠ t in atTop, ∀ y : AUX,
          ∀ (D : Precision.ChartRatio G) (_legal : Precision.LocalRatio D)
            (ζ : Axes C d → PowerSeries ℂ),
          let E := fun u : Terms C d q => Rocket.stopped S Y branch F (Lodge.basisR C) Finset.univ d
            (axis C d u.1) (WilsonPositionProgramSubmittedFaces.final j) (fun v => z v ∘ child) (t,y) u.2.val.2
          ‖PowerSeries.coeff (q+ceiling C d) (XSpace.Bare.normalized (T₀ t) G
              (finite C (Z.run.step (B.index t)).p d (z (t,y) ∘ child) (T₀ t) ζ)) -
              ∑ u : Terms C d q, weight C d q ζ u * (E u : ℂ)‖ₑ ≤
            ENNReal.ofReal ((Z.run.step (B.index t)).spacing^strength) * ∑ u : Terms C d q, ‖weight C d q ζ u‖ₑ) ∧
        ∀ {l : ℕ} (child : Fin l → Fin n), Function.Injective child →
        ∀ (d : ℕ) (v : Fin l→Dframe.Toon G d) (μ : ℝ) (k : ℕ), k≤p →
        ∃ E : ℝ, 0<E ∧ ∀ᶠ t in atTop, ∀ y : AUX, ∀ cap (P : Handoff.Directory Z (B.index t) cap),
          Handoff.Directory.budget G l d + k ≤ cap →
          let e := fun x : Ω₀ => (Z.run.step (B.index x.1)).spacing
          let θ := fun x => μ+Real.log (e x)
          ‖PowerSeries.coeff k (Rocket.adjust S Y branch F (Lodge.basisR C)
            (WilsonPositionProgramSubmittedCoefficient.final j) (Dframe.flash ∘ v) (fun x => (z x) ∘ child) Q θ e (t,y)) -
            WilsonPositionProgramPoint.entry Z (T:=T) P d μ ((z (t,y)) ∘ child) (Dframe.fill v) k‖ ≤
            E*(e (t,y))^Tide.mildG := by
  obtain ⟨_,_,stage,run⟩ := WilsonPositionProgramArithmeticCompactStrength.original (X:=Ω₀) C Z.run first paid slow branch p color nonempty K compact
  obtain ⟨stage₂,convert⟩ := WilsonPositionProgramArithmeticBookedDirectory.original (X:=Ω₀) C first paid slow branch p color Z matchMS nonempty K compact apart
  obtain ⟨H,hH,stage₃,shared⟩ := WilsonPositionProgramSharedInversionTariff.original (X:=Ω₀) C Z.run
    first paid slow branch p color nonempty K compact
  let level := max stage (max stage₂ stage₃)
  have living : stage ≤ level := le_max_left ..
  have corrected : stage₂ ≤ level := (le_max_left ..).trans (le_max_right ..)
  have normal : stage₃ ≤ level := (le_max_right ..).trans (le_max_right ..)
  obtain ⟨initial⟩ := WilsonPositionProgramArithmeticReporterBand.original C Z.run simple first hd ratio pace level
  obtain ⟨B,late⟩ := WilsonPositionProgramLaterBand.original initial floor
  refine ⟨level,B,late,?_⟩
  intro m j w S z c hc hz
  obtain ⟨F,file,_⟩ := run m j (fun u => B.index u.1) w
    (fun u => B.blocks u.1) (fun u => B.extent u.1) (fun u => living.trans (B.ready u.1)) z c hc hz
  refine ⟨F,file,?_,?_⟩
  · intro I _ _ child d tree k hk strength
    obtain ⟨cutoff,rate⟩ := shared m j (fun u=>B.index u.1) w
      (fun u=>B.blocks u.1) (fun u=>B.extent u.1) (fun u=>normal.trans (B.ready u.1))
      z c hc hz F file I child d (fun u=>tree u.1) k hk strength
    filter_upwards [B.cofinal.eventually_ge_atTop cutoff] with t due
    exact fun y => rate (t,y) due (B.mature t) (B.age t)
  · intro l child distinct d v μ k hk
    obtain ⟨E,pos,cut,estimate⟩ := convert m j w (fun u => B.index u.1)
      (fun u => B.blocks u.1) (fun u => B.extent u.1) (fun u => corrected.trans (B.ready u.1))
      F file z c hc hz child distinct d v μ k hk Q calibration
    refine ⟨E,pos,?_⟩
    filter_upwards [B.cofinal.eventually_ge_atTop cut] with t due
    exact fun y => estimate (t,y) due (B.mature t) (B.age t)
end YM.Integration.WilsonPositionProgramSharedEpoch
end
