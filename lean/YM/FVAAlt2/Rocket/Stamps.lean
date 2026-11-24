import YM.FVAAlt2.Rocket.Roots
import YM.RegulatorIR.Clocks.Test
/-! # Generate stencil score even without prepricing at a demanded cutoff
    `Exists kick ...` uses same SectionData & oriented basis and same Raw Beta-Laurent scheme
    as unadjusted Wilson elementary columns. Accepts arbitrary placements including clustered, any
    number of points in this fixed S. Symbol support costs paid by TRUE relative dispersion
    however large in native units, stored in the explicit Meter. Useful for softening by more
    steps. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Kick
open Set Filter MeasureTheory Function Finset
open PertExtension Series Series.Radial Series.Tested Chart Orb
open Budget Budget.Tariff Budget.Premium Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Spatial
open Binding Diagram.Formal Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace
open Lattice Gauge Geometry Geometry.Field Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Halo Halo.Sight Gain Profiles
open Labels Source
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X Y I:Type}{u a b p d:ℕ}{n:Side}{L: Meter X}
attribute [local instance] Gauge.frobInner
local notation "K"=> Foot G
-- aboard, literal group kernels for comparable Fk.
lemma stamp_unit : LocalStamp (G:=G) 1 0:= ⟨⟨continuous_const,fun _ _ _=>rfl,fun _ _ _ _ _ _=>contDiffAt_const⟩,⟨∅,fun _ _ _ _=>rfl⟩,fun _=>bill_const 1⟩
structure Kick (L:Meter X)(x:X→Room)(m:ℕ)(V:X→ Portrait G)(T:X→ Orders (Foot G)) : Prop where
   authority j : Halo.BasisT m m (V j) (T j)
   census j : Ranks m (T j)
   paid (p u:ℕ) : Cheap L u p x T
-- carrying the position BEFORE projections
structure Nearest (x:X→Room)(L:Meter X)(n: X→ Cover) : Prop where
   ht:Poly L fun i=> ENNReal.ofReal (dist (x i) (Motion.slide 1 (n i)))
variable {x:X→Room}
lemma kick (v: Portrait G)(h:LocalStamp v d) {y:X→ Cover}(ht:Nearest x L y): ∃ t:X→ Orders K, Kick L x d (fun j=> convey (y j) v) t :=by
    obtain ⟨B,h,hb⟩:= Profiles.stamp_symbol h
    refine ⟨fun j e r=> echo (carryX (y j)) (B e r), ⟨fun j=> h.vayne _, fun j i r hr=> hb i r ?_,fun p u=> prepaid ht.ht u (fun e _ j=> h.canopy e j)⟩⟩
    intro hh; apply hr; rw [hh]; rfl
lemma kick_unit (ht:∃ y,Nearest x L y): ∃ w:X→ Orders K, Kick L x 0 (fun _=> (1:Portrait G)) w:=by
    obtain ⟨y,h⟩:=ht; exact kick 1 stamp_unit h
lemma Kick.pair {V W:X→Portrait G}{A B:X→Orders K}(h:Kick L x a V A)(hh:Kick L x b W B): Kick L x (a+b) (fun i=>V i*W i) (fun i=>accord (A i) (B i)):=⟨fun i=> Profiles.BasisT.united (h.authority i) (hh.authority i) (h.census i) (hh.census i),fun i=> accord_rank (h.census i) (hh.census i),fun p u=> (h.paid p u).choice (hh.paid p u)⟩
lemma hands (ht:∃ y,Nearest x L y)(s:Finset I)(v:I→X→Cover)(V:I→ Portrait G)(m:I→ℕ)(hq:∀ i∈s,LocalStamp (V i) (m i))(hp:∀ i∈s,Nearest x L (v i)): ∃ w:X→ Orders K, Kick L x (∑ i∈s,m i) (fun j=>∏ i∈s, convey (v i j) (V i)) w:=by
    induction s using Finset.induction_on with
    | empty=> simpa using! (kick_unit (G:=G) ht)
    | insert i s hi ih=>
       obtain ⟨A,hA⟩:= ih (fun j hj=>hq j (mem_insert_of_mem hj)) (fun j hj=> hp j (mem_insert_of_mem hj))
       obtain ⟨B,hB⟩:= kick _ (hq i (mem_insert_self ..)) (hp i (mem_insert_self ..)); rw [Finset.sum_insert hi];simp_rw [Finset.prod_insert hi]
       exact ⟨_,hB.pair hA ⟩
end YM.RegulatorIR.FVAAlt2.Kick
