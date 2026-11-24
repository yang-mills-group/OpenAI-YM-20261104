import YM.X.Clear.Torus
import YM.Pert.Align.Schedule
import YM.PertExtension.CurveLimit
/-!
The itinerary for the large even regulators. Use compact-center succession within widths n/8..n/4. Use true side even.
Define filter-free natural supersmall error and polynomial budgets to be uniform via later sequential arguments. Not estimates on couplings.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Interval
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension LatticePT
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Pointwise Classical
variable {G:Gauge} (q:ℕ+) {R: Side} {j:ℕ} {n:ℕ}
open Pert.Align

def turns (k : ℕ): Side:=⟨8*q.val*q.val^(k^2),by positivity⟩
lemma turns_eq (k:ℕ) : ((turns q k).val:ℝ)= period q k:= by unfold turns; rw [period_eq]; dsimp; push_cast; rfl
lemma cane (k:ℕ) : magnify q k ≥ 1:=one_le_pow₀ (Nat.one_le_cast.mpr q.pos)
variable {q}
variable (hq:1<q.val)
lemma amp_pos (q:ℕ+)(j):0< magnify q j:=zero_lt_one.trans_le (cane q j)
lemma eps_eq (q:ℕ+)(i) : epsilon q i=(magnify q i)⁻¹:= rfl
include hq
lemma giant : Tendsto (magnify q) atTop atTop:= tendsto_pow_atTop_atTop_of_one_lt (L_pos q hq)
lemma runaway (d : ℕ): Tendsto (fun k:ℕ=> ((side q k).val:ℝ)* (epsilon q k)^d) atTop atTop := by
   have H:= side_rate hq d; let f:=fun k:ℕ=> magnify q k^d/ ((side q k).val:ℝ); have hh (k:ℕ):0<f k:= by unfold f; positivity
   have hh' : Tendsto f atTop (𝓝[>] 0):= tendsto_inf.mpr ⟨H,tendsto_principal.mpr (Eventually.of_forall hh)⟩
   apply (tendsto_inv_nhdsGT_zero.comp hh').congr; intro k; dsimp [f]; rw [eps_eq,inv_pow, inv_div]; rfl

def paths (hq:1<q.val) : Itinerary where
   period := side q
   gap := epsilon q
   grid := turns q
   grid_eq := turns_eq q
   positive:= epsilon_pos q
   clears:= tendsto_natCast_atTop_iff (R:=ℝ) |>.mp ((runaway hq 1).congr (fun k=> by rw [pow_one]; exact (turns_eq q k).symm))
   cutoff:= (epsilon_zero hq).mono_right nhdsWithin_le_nhds
   huge:= runaway hq
   even_at:= side_even q
end YM.PositionX.Interval
