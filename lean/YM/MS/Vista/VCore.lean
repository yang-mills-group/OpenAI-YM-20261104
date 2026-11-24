import YM.MS.Vista.Branches
/-!
# Bulk comparison all below endpoint. No Estimate.C interruptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E: Type}{L:I→Side}{M: Visa I}{P:Belt I}{K V:Planet G I}{X Y: Rake.Site G I}{F H D:Glade G I}{Z:Lin I}
    {f:ℕ→I→Law G}{ b c:Bool}{n:ℕ}{A:I→Cover} {x:P.time→ℝ}
structure Core (Z:Lin I)(K:Planet G I)(X:Rake.Site G I)(f:ℕ→I→Law G): Prop where
   h : Glow K
   script : Script Z K f X
   entry n: Knits ( X n )
local notation "Μ"=> Mid M L
local notation "Ω"=>enterV L b
abbrev bulk (P:Belt I)(X:Rake.Site G I): Prop:= ∀ n,0<n→ χr P n X
variable (S: Core (enterV L b) K X f)( T:Core ( outside L ) V Y f)(P0:Piece ( Mid M L ) K 1)( B1:bulk (Mid M L) Y)(W:stepOne M L K V)
omit S T P0 B1 W -- only include if needed
lemma bud_plus (h: WarpHere b c P ( F-H ) x)(hv: WarpHere b c P H x): WarpHere b c P F x:= by nth_rw 1 [← sub_add_cancel F H]; unfold WarpHere; rw [map_add]; exact Lease.plus h hv
lemma good_η (P:Belt I): goodM P 4=rateS P 4:= gearZ _ (4:ℤ) -- cast
abbrev Bil (S:Belt I)(L:I→Side)(k:ℕ): S.time→ℝ:= rateS S 4 * gainQ S L k
abbrev DoubleB (B:Visa I)( L:I→Side)(b c:Bool)(F:Glade G I): Prop:= ∀ k, WarpHere b c ( Mid B L ) F ( Bil (Mid B L) L k)
include P0 B1 W
lemma hill (n k:ℕ)(hp:∀ i,i<n→0 < i → χr Μ i X ∧ DoubleB M L true true ( X i-Y i )): HandC true false Μ ( ( (2:ℂ)⁻¹ ) • ( groups K X X n-groups V Y Y n )) ( Bil Μ L k ):= by
   apply fancy; unfold groups pathU; rw [ ← Finset.sum_sub_distrib ]; apply Cuba _ ( joy (rateC _ _) ( gain_pos _ _ _) ); intro i h; obtain he:= early _ _ _ h; have hi:n - i>0:=(by omega); exact step_acc P0 W ( (hp _ (by omega: n-i<n) hi).1 ) ( hp ( n-i ) (by omega) hi|>.2 k ) ( B1 i (by omega) ) ( hp i (by omega) (by omega)|>.2 k ) (rateC _ _) ( gain_pos _ _ _ )
include S T
lemma Mundane (hz:0<n): χr Μ n X ∧ DoubleB M L true true (X n-Y n) := by
   induction n using Nat.strong_induction_on with| h n ih=>
      suffices hh : DoubleB M L true true ( X n-Y n ) from ⟨ bud_plus ( by obtain ht:=hh 0; unfold Bil at ht; rw [gain0, mul_one] at ht; exact ht ) ( B1 n hz ),hh ⟩; -- B1?. hh k0 cast
      let P:= Mid M L; intro k; let v:=k+4; let u:=Bil Μ L v; let F:= X n; let H:= Y n;
      have ht: LookS (warp0 G I (F-H)) (bend G I ( (CPlan Ω K F - CPlan (outside L) V H) + ( (2:ℂ)⁻¹) • (groups K X X n-groups V Y Y n) )):= by rw [smul_sub]; exact steered _ _ _ _ _ _ ( live_g S.h S.entry S.script hz ) ( live_g T.h T.entry T.script hz ); -- arg order
      unfold WarpHere; apply Lease.sticks ( a:=u ) _ (fun i=>?le ); rotate_left;
      · apply mul_le_mul_of_nonneg_left (gain_le (show k≤ v from (by unfold v; omega)) i) ( rateC _ _ _ )
      obtain hu : nn u:=joy (rateC _ _) (gain_pos P L _);
      have hv: Adjuster ( G:= G ) Μ true true u := by unfold u Bil; rw [ ← good_η ]; refine colony nextM.acc v (by unfold v; push_cast; simp; linarith [Nat.cast_nonneg (α:=ℝ) k])
      apply kernel (a:=(fun _=>0)) nextM.acc ht hv hu (no_credit _ hu _) ; swap; · intro i; rw [ show ( F-H ) i (τ 0)= ( F-H ) i 0 from congr_arg _ τ0, Pi.sub_apply, Pi.sub_apply]; unfold F H; rw [ S.script.2 _ hz |>.1 i,T.script.2 _ hz |>.1 i, sub_self ]; -- arg order F Let simpl.O
      intro r he hB; rw [map_add]; exact Lens.plus ( plateau (rateC _ _) P0 W (S.entry n|>.1) ( T.entry n|>.1 ) hB (pinch ( B1 n hz ) (fun _=> by omega)) ) ( pinch ( hill P0 B1 W n v ih ) ( fun h=> Bool.noConfusion h )) -- hB defeq.U.
end YM.MS.Vista
