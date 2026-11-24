import YM.MS.Motif.Channel
import YM.MS.Motif.Vary

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts
open scoped Topology ContDiff
variable {A:Type} {G:Gauge} {n:ℕ} {F H:Rack G n} {b:Bool} {k:Chan G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
abbrev fieldSection (b:Bool)(F:Rack G n): Prop:=∀ k i, D (onX (!b) k,i) F=0
def dot (v:Chan G n→ Rack G n): Op ( Shore G n ) ℂ:= ∑ i:Chan G n, quash parity (onX false i) (v i)
/-- Odd vector input at unstar -/
structure Lamp (v: Chan G n→Rack G n): Prop where
   being i : Pure S (true ^^ parity (onX false i)) (v i)
   onlyA i: fieldSection false (v i)
abbrev leaf (a:Cfield G n): Rack G n:= Motif.note a (fun _=>1)
local infixl:67 "⋄"=> product S
def cape (v:Chan G n→ Rack G n): Rack G n:= ∑ i:Chan G n, phase i • (leaf (onX true i) ⋄ (v i))
variable {v:Chan G n→ Rack G n} (hv:Lamp v)
include hv in
lemma dot_pair (h:Pure S b F) : dot v (F ⋄ H)= (dot v F)⋄ H + (cross true b:ℂ) • (F ⋄ dot v H):= by unfold dot; simp only [LinearMap.sum_apply,map_sum, Finset.smul_sum, LinearMap.sum_apply,← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i hi=> q_prod (hv.being i) h
omit hv in
lemma dot_moment (s:SectorP n→+ ℂ): dot v (moment s F)=moment s (dot v F):= by unfold dot; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun i hi=> (momentum_op _).symm
omit hv in
lemma dot_call (a: Chan G n) : dot v (leaf (onX false a))=v a := by
    unfold dot; funext l; simp_rw [LinearMap.sum_apply,Finset.sum_apply,leaf,note_q,onXC]; simp
end YM.MS.Motif
