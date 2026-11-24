import YM.Integration.WilsonPositionProgramSharedEpoch
import YM.Integration.WilsonPositionProgramMasterTestCost

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramPublicMaster
open WilsonPositionProgramInversionMaterial WilsonPositionProgramSeriesRead
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Shard WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonMarkedIndependentNormalizedElection (deck)
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
    {a₀ h D₀ k u e : ℕ} (fund : ℕ → Gear G → ℝ) (income : FundedMarkedCoverRows.prices fund C.kit)
    (big : h < D₀) (rails : Rails h k u e) (l dd : Fin (a₀+1) → ℕ)
    (fit : ∀ i,l i < dd i) (cap : capP (deck (G:=G) l dd fit) ≤ k) (order : e ≤ p)
    {n : ℕ} (nonempty : 0<n) (K : Set (Points n)) (compact : IsCompact K) (apart : K⊆conf n) :
    let fields := deck (G:=G) l dd fit
    let L := C.family.path.levels
    ∃ stage, ∃ B : Band C Z.run stage, (∀ t, floor ≤ B.index t) ∧ ∃ A : ℝ, 0≤A ∧
      let m := fun u : Ω₀ => B.lower u.1
      let j := fun u : Ω₀ => B.span u.1
      let w := fun u : Ω₀ => B.powers u.1
      let S := WilsonPositionProgramInfraredCircuit.circuit C Z.run m j w (fun u => B.blocks u.1)
      ∀ (z : Ω₀ → Fin n → Cover) (c : Ω₀ → Four ℝ),
      (∀ u, c u ∈ (Z.run.step (B.index u.1)).Box) → (∀ u, (Z.run.step (B.index u.1)).rel (z u) (c u) ∈ K) →
      ∃ F : Tent j, Notebook S Y G branch color (Rocket.native j) F p ∧
        (∀ (child : Fin (a₀+1) → Fin n) (T₀ : ∀ t, (Z.run.step (B.index t)).p.Tree)
          (q : ℕ), q ≤ e → ∀ strength : ℕ, ∀ᶠ t in atTop, ∀ y : AUX,
          ∀ (D : Precision.ChartRatio G) (_legal : Precision.LocalRatio D)
            (X : Herit fields) (probe : (i : Fin (a₀+1))→Volume (dd i)),
          let m₀ := B.reporter+t
          let top := m₀+B.upper t
          let x := fun i => PermuteLens L C.metals.O (fields i) top m₀ (X i)
          let field := fun i=>steep L C.metals.O (fields i).ans (fields i).path top m₀ (top-m₀) (x i)
          let ζ := dose C l field dd fit probe
          let E := fun u : Terms C l q => Rocket.stopped S Y branch F (Lodge.basisR C) Finset.univ l
            (axis C l u.1) (WilsonPositionProgramSubmittedFaces.final j) (fun v => z v ∘ child) (t,y) u.2.val.2
          ‖PowerSeries.coeff (q+ceiling C l) (XSpace.Bare.normalized (T₀ t) G
              (finite C (Z.run.step (B.index t)).p l (z (t,y) ∘ child) (T₀ t) ζ)) -
              ∑ u : Terms C l q, weight C l q ζ u * (E u : ℂ)‖ₑ ≤
            ENNReal.ofReal (A*((Z.run.step (B.index t)).spacing)^strength*
              ∑ u : Terms C l q, ∏ i, WilsonPositionProgramNormalizedMaster.fee X e i *
                ‖jewelBloom (fit i) (u.1 i) (probe i)‖)) ∧
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
  intro fields L
  obtain ⟨loss,valued⟩ := WilsonPositionProgramMasterTestCost.original C simple fund income big rails l dd fit cap
  obtain ⟨stage,B,floorMet,commission⟩ := WilsonPositionProgramSharedEpoch.original (AUX:=AUX)
    C first paid slow branch p color Z matchMS Q calibration floor hd ratio pace nonempty K compact apart
  obtain ⟨A,Apos,affordable⟩ := valued Z.run B
  refine ⟨stage,B,floorMet,A,Apos,?_⟩
  intro m j w S z c hc hz
  obtain ⟨F,file,shared,changed⟩ := commission z c hc hz
  refine ⟨F,file,?_,changed⟩
  intro child T₀ q hq strength
  filter_upwards [shared (Fin (a₀+1)) child l T₀ q (hq.trans order) (strength+loss),affordable] with t room fee
  intro y D legal X probe
  exact (room y D legal _).trans (fee X probe q hq strength)
end YM.Integration.WilsonPositionProgramPublicMaster
end
