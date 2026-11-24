import YM.Integration.WilsonPositionProgramGroundFlight
import YM.Integration.WilsonPositionProgramSharedInversionTariff

/-! The genuine occupied course on a finite side reads the full angular and
coupling bank at the capture page. Its lifted packet converges to the
chronological covered packet in the full unweighted absolute norm. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramCapturedAngular
open Function Filter Finset Lattice Wilson Exterior Precision Marker Comparison.RG02
open RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open RegulatorIR.Budget RegulatorIR.Budget.FVAAlt2.Wind RegulatorIR.Budget.FVAAlt2.Wind.Pine
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Sound
open scoped Topology BigOperators ENNReal Classical
variable {G:Gauge} (C:Run G) (D:XSpace.Run) {X:Type} (m j:X→ℕ) (w:X→ℕ→ℕ)
  (blocks:∀x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
  (branch:∀P:RG.Patch,P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
variable (F:Tent j) {I:Type} [Fintype I] [LinearOrder I] (z:X→I → Cover) (d:I→ℕ)
  (a:(i:I)→(C.family.labels.level (d i)).Index) (b:Ledger.Choice j) (x:X)

def lifted (e r per:ℕ) :=
  Near.Lifted (Γ:=C.family.path) ((H).vol (b.choose x)) per
    (See.observe branch K H (Sound.Figure.prop C z d a) (sheet F) per (b.choose x)) e r

def originalRow (e r:ℕ) :=
  (Rocket.Ignite E Y branch F (Lodge.basisR C) univ d a z).main (b.choose x) e r

theorem absolute (e r:ℕ) : above atTop (originalRow C D m j w blocks branch F z d a b x e r)
    (lifted C D m j w blocks branch F z d a b x e r) :=
  (Near.activeM Y branch K H (sheet F) (Sound.Figure.prop C z d a) (b.choose x)).walks e r

theorem original {p:ℕ} (color:G.ColorIndex) (file:Notebook E Y G branch color (Rocket.native j) F p) :
    ∃ T:See.Times (sheet F) p, ∀(A:Type)[DecidableEq A][Fintype A](mask:Marker.Census A)(u:A),
    ∃ V:(per:ℕ)→Sound.Figure.Activation (I:=I) C H per mask,
      (∀per,Sound.Figure.Course C H z (sheet F) per u mask p T (V per)) ∧
      (∀per (dir:fieldDir G (C.family.side ((H).vol (b.choose x)) per) 1) e, e≤p →
        See.noseC mask u (T.cloth (b.choose x)) ((V per d a) (b.choose x)) e dir =
          Booth.Uniforms.cuff (See.observe branch K H (Sound.Figure.prop C z d a) (sheet F) per (b.choose x))
            (Kick.depthF univ d a) e dir) ∧
      ∀e r, Tendsto (fun per=>cost (lifted C D m j w blocks branch F z d a b x e r per -
        originalRow C D m j w blocks branch F z d a b x e r)) atTop (𝓝 0) := by
  have top:=Sound.flatTop Y branch file
  obtain ⟨T,_⟩:=See.prices (sheet F) p top
  refine ⟨T,?_⟩
  intro A _ _ mask u
  choose V course using fun per=>Sound.Figure.universal C branch Y H z (sheet F) per u mask p T top
  refine ⟨V,course,?_,?_⟩
  · intro per dir e ehi
    exact (See.observes Y branch K H mask u (Sound.Figure.prop C z d a) (sheet F) per p T top
      (course per d a) (b.choose x) dir ehi).1
  · intro e r
    exact (absolute C D m j w blocks branch F z d a b x e r).choose_spec.up

end YM.Integration.WilsonPositionProgramCapturedAngular
end
