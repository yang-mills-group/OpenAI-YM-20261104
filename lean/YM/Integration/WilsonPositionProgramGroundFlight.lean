import YM.Integration.WilsonPositionProgramFilmGroundPath
import YM.Integration.WilsonPositionProgramDeclaredForest

/-! The registered zero row is the actual iterated finite Gaussian including
its nonzero affine images. Its report at any scheduled page has the original
outer-period reading, for a whole product or any of its proper faces. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramGroundFlight
open Function Filter Finset Lattice Wilson Exterior Precision Marker Comparison.RG02
open RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Sound
open scoped Topology BigOperators Classical
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X→ℕ) (w : X→ℕ→ℕ)
    (blocks : ∀ x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
    (branch : ∀ P : RG.Patch,P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

def tested {I : Type} [LinearOrder I] [Fintype I] {A:Type} [DecidableEq A] [Fintype A]
    (S : Marker.Census A) (u:A) (z : X → I → Cover) (d:I→ℕ)
    (a:(i:I)→(C.family.labels.level (d i)).Index) (station : Ledger.Choice j) (x:X) (per:ℕ) : ℂ :=
  WilsonPositionProgramFilmGroundPath.path K H S u (Sound.Figure.prop C z d a) per (station.choose x) 0

theorem original {r:ℕ} (color:G.ColorIndex) (F:Tent j) (file:Notebook E Y G branch color (Rocket.native j) F r)
    {I : Type} [LinearOrder I] [Fintype I] {A:Type} [DecidableEq A] [Fintype A]
    (S : Marker.Census A) (u:A) (z : X → I → Cover) (d:I→ℕ)
    (a:(i:I)→(C.family.labels.level (d i)).Index) (station:Ledger.Choice j) (x:X) :
    Tendsto (tested C D m j w blocks S u z d a station x) atTop
      (𝓝 ((Rocket.stopped E Y branch F (Lodge.basisR C) univ d a station z x 0:ℝ):ℂ)) := by
  have start := Sound.flatTop Y branch file
  obtain ⟨T,_⟩ := See.prices (sheet F) r start
  have limit := Sound.Figure.green C branch Y H z F station x d a 0
  simp only [Sound.Figure.innerV,Sound.Figure.perRead,PowerSeries.coeff_mk] at limit
  apply limit.congr'
  filter_upwards with per
  let src := Sound.Figure.prop C z d a
  obtain ⟨V,book⟩ := See.hire Y branch K H S u src (sheet F) per r T start
  let page := station.choose x
  have coin := Sound.gold Y branch K H src (sheet F) start per S u page T V book 0 (Nat.zero_le r)
  simp only [Sound.coins,PowerSeries.coeff_mk,if_pos (Nat.zero_le r)] at coin
  apply coin.symm.trans
  change See.noseC S u (T.cloth page) (V page) 0 0 = _
  rw [WilsonPositionProgramFilmGround.reading _ _ _ _ ((book.allows page).1.suppose_mark _)]
  exact WilsonPositionProgramFilmGroundPath.original K H S u src (sheet F) per r T V book page 0

end YM.Integration.WilsonPositionProgramGroundFlight
end
