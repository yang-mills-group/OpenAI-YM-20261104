import YM.Integration.WilsonPositionProgramArithmetic
import YM.Integration.WilsonPositionProgramArithmeticMaterial
import YM.Integration.WilsonPositionProgramArithmeticBand
import YM.Integration.WilsonPositionProgramBookedPrescription
import YM.Integration.WilsonPositionProgramBookedDirectory
import YM.Integration.WilsonPositionProgramCompactStrength

/-! The original position construction on a run with the two arithmetic receipts.
The same native blocks, circuits, prescriptions and tests are retained in each publication. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticBookedPrescription
open WilsonPositionProgramBookedPrescription
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

include first paid slow in
/- Every subroster uses the already filed notebook and the original
polynomial source and curvature registry. The ambient compact placement
supplies a root also when the submitted subroster is empty. -/
theorem original {n : ℕ} (nonempty : 0<n) (K : Set (Points n)) (compact : IsCompact K) :
    ∃ H : ℝ, 0≤H ∧ ∃ start : ℕ, ∀ (m j : X→ℕ) (w : X→ℕ→ℕ) (i : X→ℕ)
      (blocks : ∀ x t, (C.family.S.block (m x+t)).val = D.ratio^(w x t))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀ x, start ≤ m x) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      ∀ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p →
        ∀ (z : X → Fin n → Cover) (c : X → Four ℝ),
          (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
          ∀ (I : Type) [LinearOrder I] [Fintype I] (child : I → Fin n)
            {deck : MS.Local.Physical.Deck G} (labels : I → MS.Rake.Label deck) (Q : MS.Land.Prescription deck) (μ : ℝ)
          (q : ℕ), q≤p → ∀ strength : ℕ, ∃ threshold : ℕ, ∀ x, threshold ≤ i x →
          1≤ C.family.path.levels.clock.hatBeta (m x) → RG16.Lambda C.family.path.levels (m x)≤(i x:ℝ)*Real.log D.ratio →
          let ε := fun t => (D.step (i t)).spacing
          let θ := fun t => μ+Real.log (ε t)
          ‖PowerSeries.coeff q (YM.FVAAlt2.Lobby.newEra (chart G) (Lodge.basisR C) Q (θ x) labels
              (wrap (D.step (i x)).p.side ∘ ((z x) ∘ child)) (ε x)) -
            PowerSeries.coeff q (Rocket.adjust S Y Z F (Lodge.basisR C) (WilsonPositionProgramSubmittedCoefficient.final j)
              labels (fun x => (z x) ∘ child) Q θ ε x)‖ₑ ≤ ENNReal.ofReal ((ε x)^strength) := by
  obtain ⟨H,Hpos,sites⟩ := WilsonPositionProgramSubmittedGeometry.roster K compact
  obtain ⟨start,fund⟩ := WilsonPositionProgramArithmeticInfraredAtlas.purchased C D first paid slow Z p
  refine ⟨H,Hpos,start,?_⟩
  intro m j w i blocks reach old S F file z c box support I _ _ child deck labels Q μ q hq strength
  let L := WilsonPositionProgramInfraredMeter.wallet C D m j w i H
  let ε := fun t => (D.step (i t)).spacing
  let θ := fun t => μ+Real.log (ε t)
  obtain ⟨unit,small⟩ := WilsonPositionProgramInfraredCircuit.units C D m j w blocks
  have top (x) := WilsonPositionProgramInfraredCircuit.fine D j w (x:=x) (i:=i x) (reach x)
  let room := fun x => center (D.step (i x)) (c x)
  have hpos (x:X) : (1/8:ℝ)*S.P x ≤ Spatial.singular (S.P x) (room x) := by
    change (1/8:ℝ)*(WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val ≤
      Spatial.singular (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val (room x)
    rw [top]
    simpa only [room,div_eq_mul_inv,mul_comm] using pin (D.step (i x)) (c x) (box x)
  have near (b : Fin n) : Nearest room L (fun x => z x b) :=
    WilsonPositionProgramInfraredMeter.displacements C D m j w i H z c (fun x => sites _ _ _ (support x)) b
  have clock := WilsonPositionProgramSubmittedClock.paid C D m j w i H
  have zero (x:X) : (WilsonPositionProgramInfraredAtlas.budget C D m j w blocks).peak (Page.opening j x)=0 := by change Real.log (S.l _)=0; rw [unit,Real.log_one]
  have scored := Rocket.funded S Y Z F (Lodge.basisR C) (WilsonPositionProgramSubmittedCoefficient.final j) (chart_ok G)
    (fund m j w blocks old) file zero unit (WilsonPositionProgramInfraredMeter.age C D m j w blocks i H)
    small simple (show RegulatorIR.Taping.quantum 1 0 ≤ Lodge.through p by dsimp [RegulatorIR.Taping.quantum,Lodge.through]; omega)
    (show (0:ℝ)<1/8 by norm_num) hpos labels (fun x => (z x) ∘ child) Q θ ε (fun y => near (child y)) ⟨_,near ⟨0,nonempty⟩⟩
    (Rocket.polyAdd (Poly.standard L (by finiteness : ‖μ‖ₑ≠⊤)) clock.2) clock.1
    (fun x => (D.step (i x)).positive.ne')
  obtain ⟨threshold,rate⟩ := WilsonPositionProgramSubmittedRate.original D C simple m j w i blocks reach Z F H (scored q hq) strength
  refine ⟨threshold,fun x hx mature wallet => ?_⟩
  have h := rate x hx mature wallet
  dsimp only at h ⊢
  simp only [map_sub] at h
  change ‖PowerSeries.coeff q (YM.FVAAlt2.Lobby.newEra (chart G) (Lodge.basisR C) Q (θ x) labels
    (wrap (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)) ∘ ((z x) ∘ child)) (ε x)) -
    PowerSeries.coeff q (Rocket.adjust S Y Z F (Lodge.basisR C) (WilsonPositionProgramSubmittedCoefficient.final j)
      labels (fun x => (z x) ∘ child) Q θ ε x)‖ₑ ≤ ENNReal.ofReal ((ε x)^strength) at h
  rw [top x] at h
  exact h

end YM.Integration.WilsonPositionProgramArithmeticBookedPrescription
end

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticBookedDirectory
open WilsonPositionProgramBookedDirectory
open Set Filter Function Finset Metric Maxwell Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2 XSpace XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Land
open scoped Classical Topology
variable {G : Gauge} (C : Run G) {simple : G.Simple} {a : Axis} {ε : ℝ}
    (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
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
  obtain ⟨_,_,stage,run⟩ := WilsonPositionProgramArithmeticBookedPrescription.original (X:=X)
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
end YM.Integration.WilsonPositionProgramArithmeticBookedDirectory
end

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticCompactStrength
open WilsonPositionProgramCompactStrength
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

open Finset WilsonThermometerPositionInversionWords WilsonPositionProgramSignedFace

private theorem weighted {I : Type} [Fintype I] (a E F : I → ℂ) :
    ‖(∑ b, a b * E b) - ∑ b, a b * F b‖ₑ ≤
      (∑ b, ‖E b - F b‖ₑ) * ∑ b, ‖a b‖ₑ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (enorm_sum_le ..).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  rw [enorm_mul,mul_comm]
  exact mul_le_mul_right (Finset.single_le_sum (fun j _ => zero_le (a:=‖a j‖ₑ)) (mem_univ b)) _
include first paid slow in
/- On one preselected compact hierarchy, all proper subsets, native fitted
columns, tests and their independent placements share the same calendar.
The true finite field amplitude is explicitly charged just once. -/
theorem original {n : ℕ} (nonempty : 0 < n) (K : Set (Points n)) (compact : IsCompact K) : ∃ H : ℝ, 0 ≤ H ∧
    ∃ start : ℕ, ∀ (m j i : X → ℕ) (w : X → ℕ → ℕ)
      (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀ x, start ≤ m x) → ∀ (z : X → Fin n → Cover) (c : X → Four ℝ),
      (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      ∃ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p ∧
        ∀ (I : Type) [Fintype I] [LinearOrder I] (child : I → Fin n)
          (d : I → ℕ) (_tree : ∀ x, (D.step (i x)).p.Tree) (k : ℕ), k ≤ p →
          ∀ strength : ℕ, ∃ cutoff : ℕ, ∀ x, cutoff ≤ i x →
            1≤C.family.path.levels.clock.hatBeta (m x) →
            RG16.Lambda C.family.path.levels (m x)≤(i x:ℝ)*Real.log D.ratio →
            ∀ (g τ : ℝ) (v : (j:I) → C.family.label (d j)) (t : I → ℂ),
          let A := fun (b : Basis C d) => amplitude C d g τ v (fun j (_ : Unit) => t j) () b
          let P := fun (b : Basis C d) => Rocket.stopped S Y Z F (Lodge.basisR C) univ
            (fun j : ↥(occupied C d b) => d j.val) (axisOf C d b) (WilsonPositionProgramSubmittedFaces.final j)
            (fun x j => z x (child j.val)) x k
          ‖reading C (D.step (i x)).p d (z x ∘ child) g τ v t k - ∑ b, A b * (P b : ℂ)‖ₑ ≤
            ENNReal.ofReal ((D.step (i x)).spacing^strength) * ∑ b, ‖A b‖ₑ := by
  obtain ⟨H,hH,start,publish⟩ := WilsonPositionProgramArithmeticSubmittedFaces.original (X:=X) C D
    first paid slow Z p color nonempty K compact
  refine ⟨H,hH,start,?_⟩
  intro m j i w blocks reach old z c box support S
  obtain ⟨F,file,parents⟩ := publish m j i w blocks reach old z c box support
  refine ⟨F,file,?_⟩
  intro I _ _ child d tree k hk strength
  let M := fun (b : Basis C d) x => PowerSeries.coeff (k+WilsonThermometerPositionInversionWords.grade C d b)
    (leaf C (D.step (i x)).p d (z x ∘ child) b (tree x))
  let P := fun (b : Basis C d) x => Rocket.stopped S Y Z F (Lodge.basisR C) univ
    (fun j : ↥(occupied C d b) => d j.val) (axisOf C d b) (WilsonPositionProgramSubmittedFaces.final j)
    (fun x j => z x (child j.val)) x k
  let E := fun (b : Basis C d) x => ‖M b x - (P b x : ℂ)‖ₑ
  have receipt := fun (b : Basis C d) => parents (↥(occupied C d b)) (fun j => child j.val)
    (fun j => d j.val) (axisOf C d b) tree k hk
  have bound := Carry.sum univ E (fun b _ => receipt b)
  obtain ⟨cutoff,rate⟩ := WilsonPositionProgramSubmittedRate.original D C simple m j w i blocks reach Z F H bound strength
  refine ⟨cutoff,?_⟩
  intro x hcut mature room g τ v t A P'
  rw [WilsonPositionProgramSignedFace.original C (D.step (i x)).p d (z x ∘ child) g τ v t (tree x) k]
  apply (weighted A (fun b => M b x) (fun b => (P b x:ℂ))).trans
  exact mul_le_mul_left (rate x hcut mature room) _

end YM.Integration.WilsonPositionProgramArithmeticCompactStrength
end
