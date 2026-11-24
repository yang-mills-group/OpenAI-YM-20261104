import YM.Integration.WilsonPositionProgramFilmGroundPath
import YM.Integration.WilsonPositionProgramDeclaredForest

/-! The original finite Wick ground at any chronological stop has the prescribed Wilson position coefficient as its outer-period limit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramFilmGroundFigure
open Exterior Wilson Precision Filter Set Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open WilsonPositionProgramVariableCircuit
open scoped Classical Topology PowerSeries
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X→ℕ) (w : X→ℕ→ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
    (branch : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel


theorem original (color:G.ColorIndex) (r:ℕ) (F:Tent j)
    (hF:Notebook E Y G branch color (Rocket.native j) F r)
    {I:Type}[LinearOrder I][Fintype I](z:X→I→ Cover)
    {A:Type}[DecidableEq A][Fintype A](mask:Marker.Census A)(u:A)
    (σ:Ledger.Choice j)(v:X)(d:I→ℕ)(a:(i:I)→(C.family.labels.level (d i)).Index):
    Tendsto (fun per:ℕ=>WilsonPositionProgramFilmGroundPath.path K H mask u
      (Sound.Figure.prop C z d a) per (σ.choose v) 0) atTop
        (𝓝 (↑(Rocket.stopped E Y branch F (Lodge.basisR C) Finset.univ d a σ z v 0):ℂ)):=by
  obtain ⟨T,school⟩:=WilsonPositionProgramDeclaredForest.original C D m j w blocks branch color r F hF
  obtain ⟨V,hV,_,_⟩:=school I z A mask u
  have start:=Sound.flatTop Y branch hF
  have g:=Sound.Figure.green C branch Y H z F σ v d a 0
  simp only [Sound.Figure.innerV,Sound.Figure.perRead,Sound.money,PowerSeries.coeff_mk] at g
  apply g.congr'
  filter_upwards with per
  have law:=hV per d a
  have actual:=WilsonPositionProgramFilmGroundPath.original K H mask u (Sound.Figure.prop C z d a)
    (sheet F) per r T (V per d a) law (σ.choose v) 0
  have read:=WilsonPositionProgramFilmGround.reading ((V per d a) (σ.choose v))
    u (T.cloth (σ.choose v)) 0 ((law.allows (σ.choose v)).1.suppose_mark _)
  have recorded:=See.scalar_here Y branch K H mask u (Sound.Figure.prop C z d a)
    (sheet F) per r T start law (σ.choose v) (Nat.zero_le r)
  exact recorded.symm.trans (read.trans actual)

end YM.Integration.WilsonPositionProgramFilmGroundFigure
end
