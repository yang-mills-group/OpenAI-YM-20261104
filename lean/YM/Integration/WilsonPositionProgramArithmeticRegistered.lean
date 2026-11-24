import YM.Integration.WilsonPositionProgramArithmetic
import YM.Integration.WilsonPositionProgramArithmeticDirectory
import YM.Integration.WilsonPositionProgramLaterBand

/-! The original position construction on a run with the two arithmetic receipts.
The same native blocks, circuits, prescriptions and tests are retained in each publication. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticRegisteredFrom
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
/- One calendar is selected before the external test, the original cutoff and
the target mesh error. At each reporter, all admitted evaluations share it. -/
theorem original (floor : ℕ) {d₀ : ℕ} (hd : 0<d₀) (ratio : Z.run.ratio=(3:ℕ)^d₀)
    (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m))
    {n : ℕ} (nonempty : 0<n) (K : Set (Points n)) (compact : IsCompact K) (apart : K⊆conf n) :
    ∃ Q : Prescription (Press.portDeck G), TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR C) (Press.portDeck G)) Q ∧
    ∃ stage, ∃ B : Band C Z.run stage, (∀ t, floor ≤ B.index t) ∧
      let m := fun u : Ω₀ => B.lower u.1
      let j := fun u : Ω₀ => B.span u.1
      let w := fun u : Ω₀ => B.powers u.1
      let S := WilsonPositionProgramInfraredCircuit.circuit C Z.run m j w (fun u => B.blocks u.1)
      ∀ (z : Ω₀ → Fin n → Cover) (c : Ω₀ → Four ℝ),
      (∀ u, c u ∈ (Z.run.step (B.index u.1)).Box) → (∀ u, (Z.run.step (B.index u.1)).rel (z u) (c u) ∈ K) →
      ∃ F : Tent j, Notebook S Y G branch color (Rocket.native j) F p ∧
        (∀ (I : Type) [Fintype I] [LinearOrder I] (child : I → Fin n)
          (d : I → ℕ) (_tree : ∀ t, (Z.run.step (B.index t)).p.Tree) (k : ℕ), k ≤ p →
        ∀ strength : ℕ, ∀ᶠ t in atTop, ∀ y : AUX,
          ∀ (g τ : ℝ) (v : (j:I) → C.family.label (d j)) (s : I → ℂ),
          let A := fun b : Basis C d => amplitude C d g τ v (fun j (_ : Unit) => s j) () b
          let P := fun (b : Basis C d) => Rocket.stopped S Y branch F (Lodge.basisR C) univ
            (fun j : ↥(occupied C d b) => d j.val) (axisOf C d b)
            (WilsonPositionProgramSubmittedFaces.final j) (fun u j => z u (child j.val)) (t,y) k
          ‖reading C (Z.run.step (B.index t)).p d (z (t,y) ∘ child) g τ v s k -
            ∑ b, A b * (P b : ℂ)‖ₑ ≤
          ENNReal.ofReal ((Z.run.step (B.index t)).spacing^strength) * ∑ b, ‖A b‖ₑ) ∧
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
  obtain ⟨Q,calibration⟩ := High_stopsPl simple M (YM.FVAAlt2.Lobby.Table (Lodge.basisR C) (Press.portDeck G))
  obtain ⟨initial⟩ := WilsonPositionProgramArithmeticReporterBand.original C Z.run simple first hd ratio pace (max stage stage₂)
  obtain ⟨B,late⟩ := WilsonPositionProgramLaterBand.original initial floor
  refine ⟨Q,calibration,max stage stage₂,B,late,?_⟩
  intro m j w S z c hc hz
  obtain ⟨F,file,seen⟩ := run m j (fun u => B.index u.1) w
    (fun u => B.blocks u.1) (fun u => B.extent u.1) (fun u => (le_max_left ..).trans (B.ready u.1)) z c hc hz
  refine ⟨F,file,?_,?_⟩
  · intro I _ _ child d tree k hk strength
    obtain ⟨cutoff,rate⟩ := seen I child d (fun u => tree u.1) k hk strength
    filter_upwards [B.cofinal.eventually_ge_atTop cutoff] with t due
    exact fun y => rate (t,y) due (B.mature t) (B.age t)
  · intro l child distinct d v μ k hk
    obtain ⟨E,pos,cut,estimate⟩ := convert m j w (fun u => B.index u.1)
      (fun u => B.blocks u.1) (fun u => B.extent u.1) (fun u => (le_max_right ..).trans (B.ready u.1))
      F file z c hc hz child distinct d v μ k hk Q calibration
    refine ⟨E,pos,?_⟩
    filter_upwards [B.cofinal.eventually_ge_atTop cut] with t due
    exact fun y => estimate (t,y) due (B.mature t) (B.age t)
end YM.Integration.WilsonPositionProgramArithmeticRegisteredFrom
end

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticPinnedPrescription
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
/- One calendar is selected before the external test, the original cutoff and
the target mesh error. At each reporter, all admitted evaluations share it. -/
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
          (d : I → ℕ) (_tree : ∀ t, (Z.run.step (B.index t)).p.Tree) (k : ℕ), k ≤ p →
        ∀ strength : ℕ, ∀ᶠ t in atTop, ∀ y : AUX,
          ∀ (g τ : ℝ) (v : (j:I) → C.family.label (d j)) (s : I → ℂ),
          let A := fun b : Basis C d => amplitude C d g τ v (fun j (_ : Unit) => s j) () b
          let P := fun (b : Basis C d) => Rocket.stopped S Y branch F (Lodge.basisR C) univ
            (fun j : ↥(occupied C d b) => d j.val) (axisOf C d b)
            (WilsonPositionProgramSubmittedFaces.final j) (fun u j => z u (child j.val)) (t,y) k
          ‖reading C (Z.run.step (B.index t)).p d (z (t,y) ∘ child) g τ v s k -
            ∑ b, A b * (P b : ℂ)‖ₑ ≤
          ENNReal.ofReal ((Z.run.step (B.index t)).spacing^strength) * ∑ b, ‖A b‖ₑ) ∧
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
  obtain ⟨initial⟩ := WilsonPositionProgramArithmeticReporterBand.original C Z.run simple first hd ratio pace (max stage stage₂)
  obtain ⟨B,late⟩ := WilsonPositionProgramLaterBand.original initial floor
  refine ⟨max stage stage₂,B,late,?_⟩
  intro m j w S z c hc hz
  obtain ⟨F,file,seen⟩ := run m j (fun u => B.index u.1) w
    (fun u => B.blocks u.1) (fun u => B.extent u.1) (fun u => (le_max_left ..).trans (B.ready u.1)) z c hc hz
  refine ⟨F,file,?_,?_⟩
  · intro I _ _ child d tree k hk strength
    obtain ⟨cutoff,rate⟩ := seen I child d (fun u => tree u.1) k hk strength
    filter_upwards [B.cofinal.eventually_ge_atTop cutoff] with t due
    exact fun y => rate (t,y) due (B.mature t) (B.age t)
  · intro l child distinct d v μ k hk
    obtain ⟨E,pos,cut,estimate⟩ := convert m j w (fun u => B.index u.1)
      (fun u => B.blocks u.1) (fun u => B.extent u.1) (fun u => (le_max_right ..).trans (B.ready u.1))
      F file z c hc hz child distinct d v μ k hk Q calibration
    refine ⟨E,pos,?_⟩
    filter_upwards [B.cofinal.eventually_ge_atTop cut] with t due
    exact fun y => estimate (t,y) due (B.mature t) (B.age t)
end YM.Integration.WilsonPositionProgramArithmeticPinnedPrescription
end
