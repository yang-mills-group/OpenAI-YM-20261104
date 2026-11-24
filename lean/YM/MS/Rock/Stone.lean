import YM.MS.Arts.Tall
import YM.MS.Rock.Wing

set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux
open Momentum Landau Arts Wire
open scoped Topology ContDiff
variable {G : Gauge} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m n : ℕ}

namespace Path
def slideA (h:m<n): SectorP m×ℝ→L[ℝ] SectorP n:= Left h.le ∘L ContinuousLinearMap.fst ℝ _ _+ (ContinuousLinearMap.snd ℝ (SectorP m) ℝ).smulRight (spray (hatch h))
def wing (z:ℂ)(U: Rip G)(F:Mob G)(W:Touch G m E) : (SectorP m×ℝ)×E→ℂ:= fun p=> Wtr z U F (slideA (Nat.lt_succ_self m) p.1) (Arts.lift (Nat.le_succ m) (sail W p.2))
def Px (m:ℕ): Measure (SectorP m):= volume
end Path
end YM.MS.Rock
