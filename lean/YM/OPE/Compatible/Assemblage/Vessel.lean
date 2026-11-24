import YM.OPE.Compatible.Assemblage.SoloAir
import YM.OPE.Sweep.Join
/-!
# Arc available after remounting

Output is eroded, and still has Arc (including precise singleton
carriers for everyone on single untouched fibers).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers.Salt
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float ManyCopies
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{G:Gauge}{n:Side}{R:Rep G n}{L:Fibers I V}{z:ℝ}
    (S:Salt V I L G n)
variable {J:I→ℝ}{w:V→ℝ} {a b c d Z :ℝ}
variable (s l k:ℕ)(η T :ℝ)
set_option quotPrecheck false
local notation "y!"=> Ribbons.Salt.scent R.p.B s (R.p.supportExponent+c) T η a b
local notation "τ" => R.p.threshold
-- retaind Towed before plum, from the same estimates supplying hk. Need quantitative Y exp small for after.
lemma parked (h:S.Breeze (τ))(hw:∀ i,0<J i)(hv:Occupancy S.grain s)(ht:0≤T)(hy:∀ i,J i*‖S.pepper i‖≤ T)(hX:0<η)(hY:η≤1)(hk:0 < k)(hS:∀ i:I,coverNumber R.p.B ({S.focus (L.bunch i),S.grain i}:Support n)≤l)(hc:0≤c)
    (hF:Towed J id S.air R.p.B (R.p.supportExponent+c) a)(hK:Towed J Prod.fst S.river R.p.B (R.p.supportExponent+c) b)
    (hP:∀ i:V,(L.contents i).card ≤ k)(hu:∀ i,w i=∏ j∈L.contents i,tow J (R.p.supportExponent+c) (η/k) l j)(hJ: ((R.p.B+R.p.B+1:ℕ):ℝ)^4*y! ≤ c) : Towed w id (S.mount τ) R.p.B R.p.supportExponent (Real.exp (y!)-1) ∧
      Towed w Prod.fst (S.soil τ) R.p.B R.p.supportExponent (Real.exp (y!)-1) :=by
   have hf := S.rate J τ _ _ η _ _ _ hw hv hy R.p.B_pos hX hY hS k hk hP a b ht hF hK (add_nonneg R.p.exponent_pos.le hc)
   exact (S.vessel τ).carries τ (S.wet _ h) _ _ _ c (y!) R.p.B hf R.p.exponent_pos.le
     (towP _ _ (η/k) _ hw (by positivity)) hu hJ

lemma transient (g:I→ℂ) (hY:g = L.shade g + L.divert g) (hs:S.pepper=L.shade g)(h:S.Breeze (τ)) (U:Config G n) :
    L.reap (play R (Bud I) S.river (fun U=>Mach (Bud I) g + ∑ i,S.air i U) U) =
      play R (Bud V) (S.soil τ) (fun U=>Mach (Bud V) (L.bypass g)+∑ i,S.mount τ i U) U:=by
    have he : Mach (Bud I) g + ∑ i,S.air i U= Mach (Bud I) (L.divert g)+(Mach (Bud I) S.pepper+∑ i,S.air i U):=by
       nth_rw 1 [hY]; rw [mach_add,hs]; abel
    unfold play; rw [map_smul]; dsimp only; rw [he,pass_add (mute ..) (by simp [Poly.part_sum,fun i=>(h.home i).sil U,mute]),mul_assoc,L.march_mach]
    rw [S.yields _ U h, ← mul_assoc (Poly.pass _), ← pass_add (mute ..) ?_ ] -- check namespace! Yields gives pass alone, not blank...
    rw [Poly.part_sum]; exact sum_eq_zero fun i _=> ((S.vessel τ).clearBurn τ (S.wet _ h) (S.turn _ h) i).sil _
end YM.MergeProof.Ribbons.Fibers.Salt
