import YM.Integration.WilsonOriginalPublicFigureRate
import YM.Integration.WilsonOriginalPublicFigureIncome
import YM.Integration.WilsonPositionProgramArithmeticRegistered
import YM.Integration.WilsonPositionProgramSharedInversionTariff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicFigureHearing
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

open WilsonOriginalPublicFigurePeriod (source)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonOriginalPublicTrialInput (vector)
variable (grades stations:Fin 3→ℕ)(fixedStop target:ℕ)(η:ℝ)(M₀:Fin 3→ℝ)
    (labels:∀a:Fin 3,ℕ×ℕ→C.family.label (grades a))
    (ahead:∀a,stations a≤fixedStop)(registered:Indexed C grades stations target η M₀ labels)
include first paid slow matchMS in
/-- One calibrated public course hears the complete measured input and the formal
input. For any finite menu of real cell placements its independent period is
fixed before both regulators of the physical source. -/
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
        (∀ (I : Type) [Fintype I] [LinearOrder I] (names : I → Fin 3) (child : I → Fin n)
            (trees : ∀t,(Z.run.step (B.index t)).p.Tree) (q:ℕ), q ≤ p → ∀ strength:ℕ,
          ∀ᶠ t in atTop, ∀ menu : Finset AUX, ∀δ:ℝ,0 < δ → ∀ᶠ inversion in atTop,
          ∀y∈menu, ∀N per:ℕ, fixedStop < N →
          let v:=(fun i:I=>vector C grades stations fixedStop target η M₀ labels ahead registered N per (names i))
          let g:=Pert.Asymptotics.regulatorRun C.family N per fixedStop
          let d:=grades ∘ names
          ‖PowerSeries.coeff q (WilsonOriginalPublicTrialNormalization.series C d g v (z (t,y) ∘ child)
              (Z.run.step (B.index t)).p (trees t))-
            ∑b,WilsonOriginalPublicTrialFigure.weight C d g v b*
              WilsonOriginalPublicFigurePeriod.shifted C d q b
                (source C Z.run m j w (fun a=>B.blocks a.1) branch F (fun x=>z x ∘ child) d (t,y) inversion)‖ₑ ≤
             (ENNReal.ofReal ((Z.run.step (B.index t)).spacing^strength)+ENNReal.ofReal δ)*
               ENNReal.ofReal (WilsonOriginalPublicFigureIncome.bill C grades stations fixedStop η M₀ names)) ∧
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
  obtain ⟨stage₄,measured⟩:=WilsonOriginalPublicFigureRate.original (X:=Ω₀) C Z.run first paid slow branch p color nonempty K compact
  let level := max stage (max stage₂ (max stage₃ stage₄))
  have living : stage ≤ level := le_max_left ..
  have corrected : stage₂ ≤ level := (le_max_left ..).trans (le_max_right ..)
  have normal : stage₃ ≤ level := (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have measuredReady : stage₄ ≤ level := (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  obtain ⟨initial⟩ := WilsonPositionProgramArithmeticReporterBand.original C Z.run simple first hd ratio pace level
  obtain ⟨B,late⟩ := WilsonPositionProgramLaterBand.original initial floor
  refine ⟨level,B,late,?_⟩
  intro m j w S z c hc hz
  obtain ⟨F,file,_⟩ := run m j (fun u => B.index u.1) w
    (fun u => B.blocks u.1) (fun u => B.extent u.1) (fun u => living.trans (B.ready u.1)) z c hc hz
  refine ⟨F,file,?_,?_,?_⟩
  · intro I _ _ names child trees q hq strength
    obtain ⟨threshold,grant⟩:=measured m j (fun x=>B.index x.1) w (fun x=>B.blocks x.1) (fun x=>B.extent x.1)
      (fun x=>measuredReady.trans (B.ready x.1)) z c hc hz F file I child (grades ∘ names)
      (fun x=>trees x.1) q hq strength
    filter_upwards [B.cofinal.eventually_ge_atTop threshold] with t report
    intro menu δ positive
    have allSites:=eventually_all_finset (l:=atTop (α:=ℕ)) menu (p:=fun y inversion=>
      ∀ (g:ℝ)(v:∀j,(C.family.labels.level ((grades ∘ names) j)).Coeff),
        ‖PowerSeries.coeff q (WilsonOriginalPublicTrialNormalization.series C (grades ∘ names) g v (z (t,y) ∘ child)
              (Z.run.step (B.index t)).p (trees t))-
            ∑b,WilsonOriginalPublicTrialFigure.weight C (grades ∘ names) g v b*
              WilsonOriginalPublicFigurePeriod.shifted C (grades ∘ names) q b
                (source C Z.run m j w (fun a=>B.blocks a.1) branch F (fun x=>z x ∘ child)
                  (grades ∘ names) (t,y) inversion)‖ₑ ≤
             (ENNReal.ofReal ((Z.run.step (B.index t)).spacing^strength)+ENNReal.ofReal δ)*
               ∑b,‖WilsonOriginalPublicTrialFigure.weight C (grades ∘ names) g v b‖ₑ)
    filter_upwards [allSites.mpr (fun y _=>grant (t,y) report (B.mature t) (B.age t) δ positive)]
      with inversion paidAt
    intro y hy N per live v g d
    refine (paidAt y hy g v).trans ?_
    gcongr
    have earned:=ENNReal.ofReal_le_ofReal (WilsonOriginalPublicFigureIncome.original C grades stations
      fixedStop target η M₀ labels ahead registered names N per live)
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _=>norm_nonneg _] at earned
    simpa only [ofReal_norm] using earned
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
end YM.Integration.WilsonOriginalPublicFigureHearing
end
