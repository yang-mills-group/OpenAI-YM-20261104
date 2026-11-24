import YM.MS.ScaleForest.Ordered
import YM.WilsonMS.Columns.LoopData

/-!
# Actual input vertices

No proxy based on the measured numbers. Supply the order-n part of the
interaction `pulseX` and of the *specified bare source optics*. These are
complete in dimension, with ghost data. `Ele` used also for sources evaluated
as combinations of basis optics. Height h is separate from slot count.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Motif Literal Mach Halo Emit Local.Physical
open scoped Topology ContDiff

variable {G : Gauge} {b : Bool} {r h : ℕ} {i : ℤ} {D : Deck G} {F : Mob G} {X : Flats G}

theorem cap_of_badge (he : Badge b (fun _ : ℂ=> F) h 0) (hf : Goods i F) :
    Cap0 b 0 i (fun _ : ℂ => F) := ⟨he.stock.choose_spec.fine,Eventually.of_forall (fun _=> zeroIssue hf)⟩

def interaction (G : Gauge) (n : ℕ) : LocalVertex G true 4 where
  rank := (n:ℤ)+2
  symbol := pulseX G n
  scaling := (invest G n).born 0
  slots := WilsonMS.LoopRank.R_action G n
  cap := cap_of_badge (invest G n) (WilsonMS.LoopRank.R_action G n)

theorem quartic_symbol (G : Gauge) : (interaction G 2).symbol=top4 G := by
  change pulseX G 2 = _
  simp [pulseX, Literal.hiss, Motif.χ]
  rfl

def withSource (σ : Literal.Box (Mob G)) {f : Detect.Law G} (he : Ele h r f σ) (n : ℕ) :
    LocalVertex G false h where
  rank := (n:ℤ)+r
  symbol := Literal.linear (Mob G) σ n
  scaling := (he.grows n).born 0
  slots := WilsonMS.LoopRank.R_Marks he n
  cap := cap_of_badge (he.grows n) (WilsonMS.LoopRank.R_Marks he n)

def label (T : Land.Booked D) (v : Land.Plaid D h) (n : ℕ) : LocalVertex G false h :=
  withSource (T.optics h v) (T.law h v) n

end YM.MS.ScaleForest
