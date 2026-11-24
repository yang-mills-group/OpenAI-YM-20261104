import YM.Integration.WilsonPositionProgramCapturedWords
import YM.Integration.WilsonPositionProgramCapturedAngular

/-! The actual group's angular polynomial determines every occupied tensor,
including the scalar. All its proper subproducts use the same funded clock. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramCapturedGroupReturn
open Function Filter Finset Lattice Wilson Exterior Precision Marker Comparison.RG02
open RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open RegulatorIR.Budget RegulatorIR.Diagram RegulatorIR.Budget.FVAAlt2.Wind RegulatorIR.Budget.FVAAlt2.Wind.Pine
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Sound
open scoped Topology BigOperators ENNReal Classical
variable {G:Gauge} (C:Run G) (D:XSpace.Run) {X:Type} (m j:X→ℕ) (w:X→ℕ→ℕ)
  (blocks:∀x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
  (branch:∀P:RG.Patch,P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
variable {p:ℕ}(F:Tent j)
variable {A:Type}[DecidableEq A](mask:Marker.Census A)(u:A)

def incoming (T:See.Times (sheet F) p) {I:Type} [LinearOrder I] [Fintype I]
    (V:(per:ℕ)→Sound.Figure.Activation (I:=I) C H per mask) (d:I→ℕ) (a:(i:I)→(C.family.labels.level (d i)).Index)
    (b:Ledger.Choice j)(x:X)(e r per:ℕ) :=
  Near.Lifted (Γ:=C.family.path) ((H).vol (b.choose x)) per
    (fun k=>WilsonPositionProgramCapturedWords.groupRows mask u (Kick.depthF univ d a) k
      (T.cloth (b.choose x)) ((V per d a) (b.choose x))) e r

omit [DecidableEq A] in
theorem original (color:G.ColorIndex)(file:Notebook E Y G branch color (Rocket.native j) F p):
    ∃T:See.Times (sheet F) p,∀(I:Type)[LinearOrder I][Fintype I](z:X→I → Cover)
    (A:Type)[DecidableEq A][Fintype A](mask:Marker.Census A)(u:A),
    ∃V:(per:ℕ)→Sound.Figure.Activation (I:=I) C H per mask,
      (∀per,Sound.Figure.Course C H z (sheet F) per u mask p T (V per)) ∧
      ∀(d:I→ℕ)(a:(i:I)→(C.family.labels.level (d i)).Index)(b:Ledger.Choice j)(x:X)(e r:ℕ), e≤p →
      above atTop (WilsonPositionProgramCapturedAngular.originalRow C D m j w blocks branch F z d a b x e r)
        (incoming C D m j w blocks F mask u T V d a b x e r) := by
  have top:=Sound.flatTop Y branch file
  obtain ⟨T,_⟩:=See.prices (sheet F) p top
  refine ⟨T,?_⟩
  intro I _ _ z A _ _ mask u
  choose V course using fun per=>Sound.Figure.universal C branch Y H z (sheet F) per u mask p T top
  refine ⟨V,course,?_⟩
  intro d a b x e r he
  have same(per:ℕ):incoming C D m j w blocks F mask u T V d a b x e r per =
      WilsonPositionProgramCapturedAngular.lifted C D m j w blocks branch F z d a b x e r per := by
    let written:=Sound.Figure.prop C z d a
    let read:=See.observe branch K H written (sheet F) per (b.choose x)
    have placed:=(See.handles Y branch K H mask u written (sheet F) per p T top (course per d a) (b.choose x)).2.1
    have extract:=WilsonPositionProgramCapturedWords.single mask u (Kick.depthF univ d a) e
      (T.cloth (b.choose x)) ((V per d a) (b.choose x)) read he placed
    change Packet.offer _ (WilsonPositionProgramCapturedWords.groupRows mask u _ _ _ _ r) = Packet.offer _ (read e r)
    rw [extract]
  simpa only [funext same] using
    WilsonPositionProgramCapturedAngular.absolute C D m j w blocks branch F z d a b x e r

end YM.Integration.WilsonPositionProgramCapturedGroupReturn
end
