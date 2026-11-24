import YM.Integration.WilsonThermometerPositionFilmOpening
import YM.Integration.WilsonThermometerPositionOrbitPayout
import YM.Integration.WilsonOriginalThermometerTopGrading
/-! Every face of the actual positioned three-source pupil enters one chronological clock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmPayout
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
local notation "faculty" => WilsonThermometerPositionFilmBank.original C D m j w blocks branch color r F hF live

include hF live in
def clock : See.Times (sheet F) r := by
  exact Classical.choose (WilsonThermometerPositionFilmBank.original C D m j w blocks branch color r F hF live)
local notation "T" => clock C D m j w blocks branch color r F hF live
variable (v₀:X) (moving:0<j v₀) (per:ℕ)
local notation "f" => WilsonThermometerPositionFilmOpening.flap v₀ moving
local notation "i" => (H).vol (f).next
local notation "n" => C.family.side (i+1) per
local notation "c" => C.family.side i per
local notation "step₀" => C.family.path.levels.clock.op i per
local notation "ker" => (K).step (i+1) i per (Nat.lt_succ_self _)
local notation "d" => WilsonOriginalThermometerPalette.levels
variable (A:Group C.family 6) (o:Fin 3 → Site (C.family.side ((WilsonPositionProgramInfraredCircuit.history C D m j w blocks).vol (WilsonThermometerPositionFilmOpening.flap v₀ moving).next+1) per)) (x:Wallet disks) (e:(Stock.census (Fin 3)).Mode)
local notation "mult" => dvd_refl (n).val
local notation "J" => Choice C d n n e.val
local notation "d₁" => (fun a:↥e.val=>d a.val)
local notation "p₀" q => coords C d o mult e.val q
local notation "v₁" q => axis C d e.val q
local notation "g" => Pert.Asymptotics.regulatorRun C.family (i+1) per (i+1)
local notation "τ" => (C.family.path.rep (i+1) per (i+1)).p.threshold
local notation "cap" => coordinates C A (i+1) (i+1) per
local notation "wt" q => (∏ a:↥e.val, dose C d g τ cap probe x a.val (q a).2)
variable {h a:ℕ} (D₁:Roots (G:=G) C.metals.p.profile C.metals.K C.metals.p.kernel)
  (Q:D₁.Tab C.rolls) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (enrolled:PlanV.Path D₁ C.alloy Q h ((WilsonPositionProgramInfraredCircuit.history C D m j w blocks).vol (WilsonThermometerPositionFilmOpening.flap v₀ moving).next+1) a π Γ)
local notation "W" => WilsonThermometerNumericalBank.bank C d o g τ cap probe mult x (π (i+1)) (tape (h+2))


section Copies
variable {b₀:Side} (origin:Fin 3→Site b₀) (dup:b₀.val ∣ (C.family.side ((WilsonPositionProgramInfraredCircuit.history C D m j w blocks).vol (WilsonThermometerPositionFilmOpening.flap v₀ moving).next+1) per).val)
    (g₀ τ₀:ℝ) (v₂:(j:Fin 3)→ C.family.label (WilsonOriginalThermometerPalette.levels j))
local notation "items" => Choice C d b₀ n e.val
local notation "site₁" q => coords C d origin dup e.val q
local notation "amount" q => (∏ a:↥e.val, dose C d g₀ τ₀ v₂ probe x a.val (q a).2)
local notation "originW" => WilsonThermometerNumericalBank.bank C d origin g₀ τ₀ v₂ probe dup x (π (i+1)) (tape (h+2))
include enrolled in
theorem frozen (archive:Extension.UV.Archive C.alloy.B) (active : a ≤ (i) + 1) (σ:ℝ)
    (wallet:Fin 3→ℝ) {rent:ℝ} {order slots shelf:ℕ}
    (fleet:Scene.Armada (WilsonOriginalStarGradedScene.words C d origin σ g₀ τ₀ v₂ probe WilsonOriginalThermometerGradedPalette.positive)
       wallet d σ rent order slots shelf) (rate:0<σ) (inside : r ≤ h + 2) :
    ∃ V:(q:items)→(p:ℕ)→Sound.Figure.Activation (I:=↥e.val) C H p S,
      (∀ q p,Sound.Figure.Course C H (fun _=>site₁ q) (sheet F) p () S r T (V q p)) ∧
      (∀ q p,WilsonThermometerPositionFilmBank.Reads C D m j w blocks e.val r F T p (V q p)) ∧
      ∀ (b:Fin 2) (z:fieldDir G c 1),
        Laplace.detail (Order.ratio (Bulk.Fk ker (Halo.bios step₀) (RegulatorIR.Geometry.directive step₀) originW z r)) e b.val=
          ∑q:items,(amount q)*See.noseC S () ((T).cloth (f).next) (V q per (d₁) (v₁ q) (f).next) b.val z := by
  have grant (q:items) := (faculty).choose_spec e.val (fun _=>site₁ q)
  choose V recorded fares using grant
  refine ⟨V,recorded,fares,?_⟩
  intro b z
  have paid:=WilsonThermometerPositionOrbitPayout.allGrades C per D₁ Q π Γ enrolled d origin dup g₀ τ₀ v₂ probe x e
    archive active σ WilsonOriginalThermometerGradedPalette.positive wallet fleet rate (Halo.bios step₀)
    (RegulatorIR.Geometry.directive step₀) z (C.family.path.levels.budget i) r inside b.val (by omega)
  rw [paid]
  refine sum_congr rfl fun q _ => congrArg ((amount q)*·) ?_
  exact (WilsonThermometerPositionFilmOpening.dated K H S () (Sound.Figure.prop C (fun _ : X=>site₁ q) (d₁) (v₁ q))
    (sheet F) per r T (V q per (d₁) (v₁ q)) (recorded q per (d₁) (v₁ q)) v₀ moving live
    (C.family.path.levels.budget i) z b).symm

end Copies

include enrolled in
theorem original (archive:Extension.UV.Archive C.alloy.B) (active : a ≤ (i) + 1) (σ:ℝ)
    (wallet:Fin 3→ℝ) {rent:ℝ} {order slots shelf:ℕ}
    (fleet:Scene.Armada (WilsonOriginalThermometerTopDensity.primitive C A (i+1) per o σ)
       wallet d σ rent order slots shelf) (rate:0<σ) (inside : r ≤ h + 2) :
    ∃ V:(q:J)→(p:ℕ)→Sound.Figure.Activation (I:=↥e.val) C H p S,
      (∀ q p,Sound.Figure.Course C H (fun _=>p₀ q) (sheet F) p () S r T (V q p)) ∧
      (∀ q p,WilsonThermometerPositionFilmBank.Reads C D m j w blocks e.val r F T p (V q p)) ∧
      ∀ (b:Fin 2) (z:fieldDir G c 1),
        Laplace.detail (Order.ratio (Bulk.Fk ker (Halo.bios step₀) (RegulatorIR.Geometry.directive step₀) W z r)) e b.val=
          ∑q:J,(wt q)*See.noseC S () ((T).cloth (f).next) (V q per (d₁) (v₁ q) (f).next) b.val z := by
  exact frozen C D m j w blocks branch color r F hF live v₀ moving per x e D₁ Q π Γ enrolled o mult g τ cap
    archive active σ wallet fleet rate inside

end YM.Integration.WilsonThermometerPositionFilmPayout
