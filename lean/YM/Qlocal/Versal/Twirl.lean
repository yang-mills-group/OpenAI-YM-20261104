import YM.Qlocal.Versal.Cactus
import YM.Qlocal.Versal.Corner
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Versal
open Function Filter Metric Lattice Laurent RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar Progress.DirectedRecipe RGComparison01 AllOrder AllOrder.Burn AllOrder.Till
open Quipu Quipu.Lasso Quipu.Sonnet Marker
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge}{c f C F: Side}{i j k n m r M D:ℕ}{g t d:ℝ}
  {V:Type}[DecidableEq V]{R:Marker.Census V}
variable (S:Tale R G)(X:S.Decision)(s:Senses R) (h:C.val=c.val*D) (o: V→Site C) (l:V→Site c)
set_option quotPrecheck false
local notation "H"=> (Macrame.normal (Deck.divides h) h)
local notation "P"=> Sonnet.root s
local notation "M₀"=> Macrame.splitter (Deck.divides h)
variable (he:Tale.Live o s M)(hl:∀ i∈essence s,l i=Macrame.splitter (Deck.divides h) (o i))
open Macrame Slide Deck
private lemma terminal0 (x:Site C)(w:Lattice.Walk): Lattice.stop x w∈ Lattice.visits x w:= by induction w generalizing x <;>simp_all [Lattice.visits,Lattice.stop]
include hl
lemma eclipsed (F:Bay s)(hm:k+M<c.val)(hd:F.tariff ≤ k) (he:Tale.Live o s M) : F.Hears o ↔ F.Hears l:= by
 constructor
 · intro hg i hi; rw [hl i hi, hl P (ownership s), hg i hi]; exact (H).rooted ..
 intro hg i hi
 let y':= bent (o P) (F.pursue i); let w:=Lattice.route 0 (F.pursue i) (Equiv.refl _); have hz : stop (o P) w=y':= (floor_st ..).trans (congr_arg _ (route_end ..)); have hx: y'∈ Crown w (o P):= by rw [found_crown,List.mem_toFinset, ← hz]; exact terminal0 ..  -- adjust
 have hQ : separation (o P) y' ≤ k:= le_trans (Vase.walks_first (o P) y' w hx) (by unfold w; rw [Stationary.route_length,sub_zero]; exact (F.stable i hi).trans hd)
 apply Deck.tiniest (Deck.divides h)
 · exact (hl i hi).symm.trans ((hg i hi).trans ((congr_arg (fun x:Site c=>bent x (F.pursue i)) (hl P (ownership s))).trans ((H).rooted ..).symm))
 apply Nat.lt_of_le_of_lt (separation_triangle _ (o P) _) ?_; have h1:=he i hi; change _+separation (o P) y' < _; rw [separation_comm (o i)]; omega
include he
-- prescription transfer only for relevant s (even if inactive on this input but charged); § actual short. T applies arbitrary inactive policy but requires radius at high. Mask funding separately.
lemma precedes (hm:k+M < c.val) (U:Config G c): S.wake s (Tale.short S X k) l g U = S.wake s (Tale.short S X k) o g ((H).links U):= by
 unfold Tale.wake; simp only [Finset.sum_apply, Tale.termR,Pi.smul_apply]; apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl fun j _=>?_ ; apply congr_arg; unfold Tale.playing Album.picture Album.realize; apply tsum_congr; intro q; unfold Album.readout; let F':=(S.array s i j q); let P':=F'.stage; by_cases hX : (Tale.short S X k) s i j q; swap; · rw [if_neg (mt And.left hX),if_neg (mt And.left hX)]; rfl
 have hu:= eclipsed s h o l hl P' hm (le_trans (Nat.le_add_left F'.stage.tariff F'.reach) hX.2) he; by_cases hp:P'.Hears l; swap; · rw [if_neg (mt And.right hp),if_neg (mt And.right (mt hu.mp hp))]; rfl
 rw [if_pos (And.intro hX hp),if_pos (And.intro hX (hu.mpr hp)),Vase.read,Vase.read,(H).expansion, hl P (ownership s)]; rfl
lemma low : Tale.Live l s M:=by intro i hi; rw [hl P (ownership s),hl i hi]; exact (Deck.less (Deck.divides h) ..).trans (he i hi)
lemma turn_t (hz: 2*M<c.val): Tale.Live o s k ↔ Tale.Live l s k:= by
 constructor; · exact fun h9=>low s h o l h9 hl -- h0
 intro hl0 i hi; apply Eq.trans_le ?_ (hl0 i hi); rw [hl i hi, hl P (ownership s)]; exact teaches (Deck.divides h) _ _ (by have hu:=he i hi; omega)
end YM.Qlocal.Versal
