import YM.Qlocal.Quipu.Sequel
import YM.AllOrder.Ker.Live
/-!
# Root assignment to coarse projection ON THE SAME hierarchical Patch
Ticket-e Plan uses License loans even though #locations large.O.Cache.
Keep residue in parameters for all stamps and re-expression through Atlas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c f:Side} {S:StepData c f}{d t a v u C:ℝ}{R:Census V}
open Album Lagger Binding Turbin Primitives.TwoWave Primitives.TwoWave.RealSlice AllOrder.Ker Lasso
namespace Arbor
variable (S) {s:Senses R} (t:Places s c) (m:Bay s) (p:V→Site S.ratio.count)(x: Site c)
abbrev pivot (s:Senses R) : ↥(essence s):= ⟨Sonnet.root s, ownership s⟩
abbrev zstar (s:Senses R)(p:V→Site S.ratio.count)(x:Site c):= S.ratio.assemble (x,p (Sonnet.root s))
abbrev drew := assign S p (Sonnet.fill s t)
local notation "Z"=> zstar S s p
local notation "X"=> drew S t p
abbrev orient (m:Bay s) (p:V→Site S.ratio.count)(x:Site c)(v:V):= bent (zstar S s p x) (m.pursue v)
local notation "Ψ"=> orient S m p x
abbrev family (m:Bay s) (p:V→Site S.ratio.count)(x:Site c): Places s c := fun i=> S.ratio.parent (orient S m p x i.val)
local notation "H"=> family S m p x
abbrev ticket (m:Bay s) (p:V→Site S.ratio.count)(x:Site c): Prop:= ∀ i∈ essence s,S.ratio.residue (orient S m p x i)=p i
local notation "Q"=> ticket S m p x
lemma base_fill (i) (hi:i∈essence s) : drew S t p i=S.ratio.assemble (t ⟨i,hi⟩,p i):=by unfold drew assign Sonnet.fill; rw [dif_pos hi]
lemma points : drew S t p (Sonnet.root s)= Z (t (pivot s)):= base_fill S t p ..
lemma beginning : Ψ (Sonnet.root s)=Z x:=by rw [orient,bent,m.starts,map_zero,zero_add]
lemma pup : H (pivot s)=x:=by unfold family pivot; rw [beginning,S.ratio.assemble_parent]
lemma works (h:X (Sonnet.root s)=Z x)(hp:Bay.Hears m X) : Q ∧ t=H := by
 have he i (hi:i∈ essence s): Ψ i=X i:= by rw [hp i hi,h] -- danger h rewrite X i root
 refine ⟨fun i hi=>?_, funext fun i=>?_ ⟩
 · rw [he i hi, base_fill S t p i hi,S.ratio.assemble_res]
 change _=S.ratio.parent (Ψ i.val); rw [he _ i.property, base_fill ..]; exact (S.ratio.assemble_parent (t i,p i)).symm -- syntax
lemma rein (h: Q) : Bay.Hears m (drew S H p):= by
 rw [Bay.Hears]; intro i hi;
 rw [points,pup,base_fill S _ p i hi]; change S.ratio.assemble (S.ratio.parent (Ψ i),p i)= _; rw [← h i hi]; exact S.ratio.unpack_at (Ψ i)
lemma memo (w:V)(h:w∈ essence s) : separation (Z x) (Ψ w)≤ m.tariff:=by
 rw [separation_comm, separation, orient, bent,add_sub_cancel_right]; exact (Next.Free.within_size ..).trans (m.stable w h)
lemma fore (w:V)(h:w∈ essence s): S.ratio.count.val*separation x (H ⟨w,h⟩)≤ m.tariff+S.ratio.count.val:=by
 change S.ratio.count.val*separation x (S.ratio.parent (Ψ w))≤ _; exact le_trans (b:=separation (Z x) (Ψ w)+_) (by have hp:=Corona.foreshorten S.ratio (Z x) (Ψ w); rw [show S.ratio.parent (Z x)= _ from (show S.ratio.parent (Z x)=x from Ratio.assemble_parent ..)] at hp; exact hp) (Nat.add_le_add_right (memo S m p x w h) _)
lemma bend (u v:Site f): let ξ:=separation (S.ratio.parent u) (S.ratio.parent v); ξ ≤ separation u v/S.ratio.count.val+1:= by
 intro y; let L:=S.ratio.count.val
 cases h:y with | zero=>exact Nat.zero_le _ | succ n=> have he:S.ratio.count.val*n ≤ separation u v:= by have hg:=Corona.foreshorten S.ratio u v; rw [show separation (S.ratio.parent u) _ = n+1 from h, Nat.mul_succ] at hg; omega
                                                       refine Nat.add_le_add_right ((Nat.le_div_iff_mul_le S.ratio.count.pos).mpr ((Nat.mul_comm ..).trans_le he)) _
section walls
open AllOrder Ker.Start Further.PhysicalPeriodLimitF933 Macrame Lace
variable {P:Patch} {n m:Side}
-- `m` Bay collision use explicitly instead
end walls
end Arbor
end YM.Qlocal.Quipu.Sonnet
