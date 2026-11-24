import YM.FormalBulk08.Avenue.Tune
import YM.FormalBulk08.Broc.Illuminate
import YM.Push.PRICE_COMPILER.Post

/-! Mathematical pre-block prices. Can combine w any other stage demands;
permits same `Wait` API as underlying construction. No future block-ratio
requirements loop back into earlier-ratio choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Borough
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler
variable {G:Gauge}{K:KernelChoices}
-- choose all stage widths *before* buying patch data; includes the
-- (alternating or crossing J) whole Tail.
structure Window (G:Gauge)(K:KernelChoices) where
    width :ℕ→ℝ
    pos:∀ i,0<width i
    bill:∀ i,width i≤ spruce K G i

def windowBasis (G:Gauge)(K:KernelChoices): Borough.Window G K:= ⟨_,spruce_pos K _,spruce_mod'⟩ where
  spruce_mod' := fun i=>le_refl (spruce K G i)
def shaded (T:Borough.Window G K)(u:ℕ→ℝ)(hp:∀ i,0<u i): Borough.Window G K:= ⟨fun i=>min (T.width i) (u i),fun i=>lt_min (T.pos i) (hp i),fun i=>(min_le_left ..).trans (T.bill i)⟩
lemma Window.lines (T:Borough.Window G K){i j:ℕ}(h:i≤j)(p:j≤ i+1):
 T.width i≤ window G K i ∧ T.width i≤joint G K i j ∧ T.width i≤Quire.coverPrice G K j i:=by
   have ht: T.width i≤ shining K G i:= (T.bill i).trans (spruce_mod ..); exact ⟨ht.trans (shining_win ..),ht.trans (shining_join K G h p),(T.bill i).trans (spruce_axis K G h p)⟩
-- finite per root.
lemma bddBill {I:Type*} [Finite I] (f:I→ℝ):∃ C:ℝ,0 ≤ C ∧ ∀ i, |f i| ≤ C:= by
   let _ := Fintype.ofFinite I; refine ⟨∑ i,|f i|,Finset.sum_nonneg (fun _ _=> abs_nonneg _),fun i=> Finset.single_le_sum (f:=fun x=>|f x|) (fun j _=> abs_nonneg _) (Finset.mem_univ _)⟩
-- At smoothing index j, admit every horizon, order & l,r etc declared in ≤j.
-- Using a slack j≥d+3 before interpretation. neighbor test horizon too.
structure Pre (K:KernelChoices)(W:Borough.Window G K)(ρ:ChartRatio G)(F:∀ d,Frame G d)(H:Hol G)(f:ℕ→ℕ):Prop where
   vacuum: ∀ E j t:ℕ,E≤j→ t ≤ j → j ≤ t+1 → costL G K (W.width j) (W.width t) (cost0 G K (W.width t) t E) ρ t j E ≤ (f j:ℝ)
   fields:∀ D E R d j t:ℕ, ∀ o:Loc G 1,d≤j→D≤j→E≤j→R≤j→ t≤j→ j≤ t+1→ preGate (F d) H K o D E R j t (W.width j) (W.width t) ≤ (f j:ℝ)
lemma funded_before (K:KernelChoices)(W:Borough.Window G K)(ρ:ChartRatio G)(F:∀ d,Frame G d)(H:Hol G) (v:ℕ→ℕ): ∃ f:ℕ→ℕ,v ≤ f ∧ Pre K W ρ F H f:= by
   let J(j:ℕ):= Fin (j+1)
   choose B hB P using fun j=> bddBill (fun p:J j × J j=> costL G K (W.width j) (W.width p.2.val) (cost0 G K (W.width p.2.val) p.2.val p.1.val) ρ p.2.val j p.1.val)
   choose C hC T using fun j=> bddBill (fun (p:J j × J j ×J j ×J j ×J j × Loc G 1)=>preGate (F p.1.val) H K p.2.2.2.2.2 p.2.1.val p.2.2.1.val p.2.2.2.1.val j p.2.2.2.2.1.val (W.width j) (W.width p.2.2.2.2.1.val))
   let f j := v j + Nat.ceil (B j+C j); refine ⟨f,fun i=> Nat.le_add_right .., ⟨?_,?_⟩⟩
   · intro E j t he ht hp; refine (le_abs_self _).trans ((P j (⟨E,Nat.lt_succ_of_le he⟩,⟨t,Nat.lt_succ_of_le ht⟩)).trans ((le_add_of_nonneg_right (hC j)).trans ((Nat.le_ceil _).trans ?_))); gcongr; exact Nat.le_add_left ..
   intro D E R d j t o hd hk he hR ht hp; refine (le_abs_self _).trans ((T j (⟨d,Nat.lt_succ_of_le hd⟩, ⟨D,Nat.lt_succ_of_le hk⟩,⟨E,Nat.lt_succ_of_le he⟩,⟨R,Nat.lt_succ_of_le hR⟩,⟨t,Nat.lt_succ_of_le ht⟩,o)).trans ((le_add_of_nonneg_left (hB j)).trans ((Nat.le_ceil _).trans ?_))); gcongr; exact Nat.le_add_left ..
end YM.FormalBulk08.Borough
