import YM.Integration.WilsonThermometerPositionFilmFaces
import YM.Integration.WilsonThermometerPositionFilmRecast

/-! The actual measured reset of the finite bank stores this very chronological face, including every occupied proper subword. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmDeposit
open Set OPE OPE.Owl
open Function Filter Finset RG Lattice Tree Wilson Exterior Precision PhysicalNext PhysicalNext.Repeat Legato
open Push Input Org Next.Scheduling Next.Scheduling.Clock ConnectedActivityE6 AnalyticBridge VerifiedReset
open RegulatorIR RegulatorIR.Binding RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open QuadraticLocal.Affinity Source Labels RG.Supply FVA1 Cells
open PertExtension.Series Geometry Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Extra.Iteration
open Comparison.RG02 Comparison.RG02.Symmetry Comparison.RG02.Cumulants
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV
open WilsonPositionProgramVariableCircuit WilsonThermometerProgramSubmittedWords
open WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open scoped Classical Topology BigOperators PowerSeries
variable {G:Gauge} (C:Run G) (D:XSpace.Run) {X:Type} (m j:X→ℕ) (w:X→ℕ→ℕ)
  (blocks:∀ x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
  (branch:∀ P:RG.Patch,P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
local notation "S" => Stock.census Unit
variable (color:G.ColorIndex) (r:ℕ) (F:Tent j)
  (hF : Notebook (WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks) (Oracle.books C.family.path.levels.clock.kernel) G branch color (Rocket.native j) F r) (live : 0 < r)
local notation "T" => WilsonThermometerPositionFilmPayout.clock C D m j w blocks branch color r F hF live
variable (v₀:X) (moving:0<j v₀) (per:ℕ)
local notation "f" => WilsonThermometerPositionFilmOpening.flap v₀ moving
local notation "i" => (H).vol (f).next
local notation "n" => C.family.side (i+1) per
local notation "c" => C.family.side i per
local notation "step₀" => C.family.path.levels.clock.op i per
local notation "ker" => (K).step (i+1) i per (Nat.lt_succ_self _)
local notation "d" => WilsonOriginalThermometerPalette.levels
variable (A:Group C.family 6) (o:Fin 3 → Site (C.family.side ((WilsonPositionProgramInfraredCircuit.history C D m j w blocks).vol (WilsonThermometerPositionFilmOpening.flap v₀ moving).next+1) per)) (x:Wallet disks)
local notation "mult" => dvd_refl (n).val
local notation "g" => Pert.Asymptotics.regulatorRun C.family (i+1) per (i+1)
local notation "τ" => (C.family.path.rep (i+1) per (i+1)).p.threshold
local notation "cap" => coordinates C A (i+1) (i+1) per
variable {h a:ℕ} (D₁:Roots (G:=G) C.metals.p.profile C.metals.K C.metals.p.kernel)
  (Q:D₁.Tab C.rolls) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (enrolled:PlanV.Path D₁ C.alloy Q h ((WilsonPositionProgramInfraredCircuit.history C D m j w blocks).vol (WilsonThermometerPositionFilmOpening.flap v₀ moving).next+1) a π Γ)
local notation "W" => WilsonThermometerNumericalBank.bank C d o g τ cap probe mult x (π (i+1)) (tape (h+2))


section Copies
variable {b₀:Side} (origin:Fin 3→Site b₀) (dup:b₀.val ∣ (C.family.side ((WilsonPositionProgramInfraredCircuit.history C D m j w blocks).vol (WilsonThermometerPositionFilmOpening.flap v₀ moving).next+1) per).val)
    (g₀ τ₀:ℝ) (v₂:(j:Fin 3)→ C.family.label (WilsonOriginalThermometerPalette.levels j))
local notation "originW" => WilsonThermometerNumericalBank.bank C d origin g₀ τ₀ v₂ probe dup x (π (i+1)) (tape (h+2))
local notation "mask" => Stock.census (Fin 3)
local notation "pool" e => Choice C d b₀ n (e).val
local notation "deg₁" e => (fun a:↥(e).val=>d a.val)
local notation "pos₁" e:max q:max => coords C d origin dup (e).val q
local notation "lab₁" e:max q:max => axis C d (e).val q
local notation "money" e:max q:max => (∏ a:↥(e).val, dose C d g₀ τ₀ v₂ probe x a.val (q a).2)
local notation "field" z => Bulk.Fk ker (Halo.bios step₀) (RegulatorIR.Geometry.directive step₀) originW z r
local notation "donor" e => (q:(pool e))→(p:ℕ)→Sound.Figure.Activation (I:=↥(e).val) C H p S
local notation "jointTerm" V:max z:max b:max => Poly.inject (R:=mask) (fun e=>∑ q:pool e,
  (money e q)*See.noseC S () ((T).cloth (f).next) (V e q per (deg₁ e) (lab₁ e q) (f).next) (b).val z)
local notation "realCost" e:max h₀:max => (QuadraticLocal.Rebirth.caliber (Γ (i+1)) (e).1).back h₀
local notation "cash" e:max h₀:max base:max => FVA1Physical.Wilson.recastColors ker (Halo.bios step₀)
  (RegulatorIR.Geometry.directive step₀) originW d r (realCost e h₀) base
include enrolled in
theorem original (archive:Extension.UV.Archive C.alloy.B) (active : a ≤ (i) + 1) (σ:ℝ)
    (wallet:Fin 3→ℝ) {rent:ℝ} {order slots shelf:ℕ}
    (fleet:Scene.Armada (WilsonOriginalStarGradedScene.words C d origin σ g₀ τ₀ v₂ probe WilsonOriginalThermometerGradedPalette.positive)
       wallet d σ rent order slots shelf) (rate:0<σ) (inside : r ≤ h + 2) (α:ℝ) (earned:Pace.Earn (Γ (i+1)) α) (depth:ℕ)
    (base:Bulk.Colors (mask) G c) :
    ∃ V:(e:(mask).Mode)→donor e,
      (∀ e q p,Sound.Figure.Course C H (fun _=>pos₁ e q) (sheet F) p () S r T (V e q p)) ∧
      (∀ e q p,WilsonThermometerPositionFilmBank.Reads C D m j w blocks e.val r F T p (V e q p)) ∧
      ∀ (z:fieldDir G c 1) (s:Hot (mask)),
        let y:=fun b:Fin 2=>jointTerm V z b
        (Air.discharge (cash earned depth base) 0 z).part s.val=(Extra.Trajectories.connected (y 0)).part s.val ∧
          (Air.discharge (cash earned depth base) 1 z).part s.val=
            (y 1 * YM.Primitives.GCC.Anchor.inverseMass (y 0)).part s.val := by
  obtain ⟨V,reg,course,reads⟩:=WilsonThermometerPositionFilmFaces.original C D m j w blocks branch color r F hF live
    v₀ moving per x D₁ Q π Γ enrolled origin dup g₀ τ₀ v₂ archive active σ wallet fleet rate inside
  refine ⟨V,reg,course,?_⟩
  intro z s
  have phase:=WilsonThermometerPositionFilmRecast.original ker (Halo.bios step₀) (RegulatorIR.Geometry.directive step₀)
    originW d r live (Γ (i+1)) α earned depth base (fun _=>rfl) s z
  exact ⟨phase.1.trans (congrArg (fun b:Poly (mask)=>b.part s.val) (reads z).1),
    phase.2.trans (congrArg (fun b:Poly (mask)=>b.part s.val) (reads z).2)⟩

end Copies
end YM.Integration.WilsonThermometerPositionFilmDeposit
