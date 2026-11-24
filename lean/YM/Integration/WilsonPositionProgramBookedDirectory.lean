import YM.Integration.WilsonPositionProgramBookedPrescription
import YM.Integration.WilsonPositionProgramSharedDirectory

/-! Price the complete chronological Wilson prescription against the signed
position directory on the same finite mesh and every proper separated face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramBookedDirectory
open Set Filter Function Finset Metric Maxwell Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2 XSpace XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Land
open scoped Classical Topology
variable {G : Gauge} (C : Run G) {simple : G.Simple} {a : Axis} {ε : ℝ}
    (first : WilsonPositionProgramNestedElection.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (branch : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
    (Z : WilsonPrescription G) {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (matchMS : Main.Match Z simple M T dial)
variable {X : Type} {n : ℕ}
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
local notation "β" => C.family.path.levels.clock.hatBeta

private def take {l : ℕ} (child : Fin l → Fin n) (x : Points n) : Points l := points fun j => x (child j)

include first paid slow matchMS in
theorem original (nonempty : 0<n) (K : Set (Points n)) (compact : IsCompact K) (away : K⊆conf n) :
    ∃ stage : ℕ, ∀ (m j : X→ℕ) (w : X→ℕ→ℕ) (i : X→ℕ)
      (blocks : ∀ x t, (C.family.S.block (m x+t)).val=Z.run.ratio^(w x t))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=Z.run.reserve*(i x)*(i x)+i x),
      (∀ x, stage ≤ m x) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C Z.run m j w blocks
      ∀ F : Tent j, Notebook S Y G branch color (Rocket.native j) F p →
      ∀ (z : X → Fin n → Cover) (c : X → Four ℝ), (∀ x, c x ∈ (Z.run.step (i x)).Box) →
      (∀ x, (Z.run.step (i x)).rel (z x) (c x) ∈ K) →
      ∀ {l : ℕ} (child : Fin l → Fin n), Injective child →
      ∀ (d : ℕ) (v : Fin l→Dframe.Toon G d) (μ : ℝ) (q : ℕ), q≤p →
      ∀ Q : Prescription (Press.portDeck G), TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR C) (Press.portDeck G)) Q →
      ∃ E : ℝ, 0<E ∧ ∃ cut : ℕ, ∀ x, cut ≤ i x → 1≤β (m x) →
        RG16.Lambda C.family.path.levels (m x)≤(i x:ℝ)*Real.log Z.run.ratio →
        ∀ cap (P : Handoff.Directory Z (i x) cap), Handoff.Directory.budget G l d + q ≤ cap →
        let e := fun t => (Z.run.step (i t)).spacing
        let θ := fun t => μ+Real.log (e t)
        ‖PowerSeries.coeff q (Rocket.adjust S Y branch F (Lodge.basisR C)
          (WilsonPositionProgramSubmittedCoefficient.final j) (Dframe.flash ∘ v) (fun t => (z t) ∘ child) Q θ e x) -
          WilsonPositionProgramPoint.entry Z (T:=T) P d μ ((z x) ∘ child) (Dframe.fill v) q‖ ≤
          E*(e x)^Tide.mildG := by
  obtain ⟨_,_,stage,run⟩ := WilsonPositionProgramBookedPrescription.original (X:=X)
    C Z.run first paid slow branch p color nonempty K compact
  refine ⟨stage,?_⟩
  intro m j w i blocks reach age S F file z c room bounds l child distinct d v μ q hq Q calibration
  obtain ⟨start,estimate⟩ := run m j w i blocks reach age F file z c room bounds (Fin l) child
    (Dframe.flash ∘ v) Q μ q hq 1
  have cont : Continuous (take child) := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun a => PiLp.continuous_apply 2 _ (child a))
  have projected : take child '' K ⊆ conf l := by
    rintro _ ⟨x,hx,rfl⟩
    exact (away hx).comp distinct
  obtain ⟨A,B,Apos,Bpos,formal⟩ := WilsonPositionProgramSharedDirectory.original C Z matchMS Q calibration d v μ q
    _ (compact.image cont) projected
  obtain ⟨date,later⟩ := eventually_atTop.mp formal
  refine ⟨A+B+1,by positivity,max start date,?_⟩
  intro x ready mature wallet cap P due e θ
  have h₁ := estimate x ((le_max_left ..).trans ready) mature wallet
  have h₂ := later (i x) ((le_max_right ..).trans ready) cap P due ((z x) ∘ child) (c x) (room x)
    ⟨(Z.run.step (i x)).rel (z x) (c x),bounds x,rfl⟩
  let middle := WilsonPositionProgramOriginalLanding.opened C Q (Dframe.flash ∘ v) μ q
    ⟨Z.run.step (i x),(z x) ∘ child,c x⟩
  let predicted := PowerSeries.coeff q (Rocket.adjust S Y branch F (Lodge.basisR C)
    (WilsonPositionProgramSubmittedCoefficient.final j) (Dframe.flash ∘ v) (fun t => (z t) ∘ child) Q θ e x)
  have h₀ : ‖predicted-middle‖ ≤ e x := by
    rw [norm_sub_rev]
    apply (ENNReal.ofReal_le_ofReal_iff (Z.run.step (i x)).positive.le).mp
    simpa only [middle,predicted,WilsonPositionProgramOriginalLanding.opened,θ,e,←ofReal_norm,pow_one] using h₁
  have cheap : e x ≤ (e x)^Tide.mildG := by
    have unit : e x ≤ 1 := inv_le_one_of_one_le₀ (show (1:ℝ) ≤ (Z.run.den (i x):ℝ) by exact_mod_cast Z.run.den_pos (i x))
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (Z.run.step (i x)).positive unit
      (show Tide.mildG ≤ 1 by norm_num)
  exact (norm_sub_le_norm_sub_add_norm_sub predicted middle _).trans
    ((add_le_add (h₀.trans cheap) h₂).trans_eq (by ring))
end YM.Integration.WilsonPositionProgramBookedDirectory
