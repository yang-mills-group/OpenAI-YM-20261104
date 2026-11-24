import YM.Qlocal.Canopy.Weeze
import YM.MergeProof.Emit
/-!
 # Real activation tallies vs prescribed log, with all couplings traversing orientations.
 Independent marked sectors (unprinted) before insertion into physical marker P. Size before
 reinflating coupling poles etc. Genuine conditional log, earnings will feed through.Staircase
 service & Aura echelons.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Canopy.Button
open Function Finset Filter Marker Merge Switch
open Comparison.RG02.Order Comparison.RG02.Cumulants Comparison.RG02.Assembly
open PertExtension PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP
open AllOrder.Response Extra.Trajectories Next.SectorChange
open scoped Topology ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
-- classical used explicitly for synthetic.S.P.+Kernel support API
open RGComparison01.Slate
local notation "n0"=> (Fintype.card ι)
abbrev universeP (ι:Type)[Fintype ι]: Census ι:= ⟨univ,mem_univ _,fun _=> mem_univ _,fun _ _ _=> mem_univ _⟩
-- needs DecEq instance? not implying.H.Meta.
local notation "X"=> universeP ι
abbrev tag (i:ι): Multi.Hot X:=⟨(X).fire i, Finset.singleton_nonempty i⟩
abbrev mat (K:Score ι): Poly X:= mapScores X (fun i:ι=> plant (R:=X) tag i) K
abbrev tile (P:Finset ι): (X).Mode:= ⟨P,mem_univ _⟩
set_option quotPrecheck false
local notation "κ"=> plant (R:=X) tag
local notation "S"=> Score ι
lemma mat_reads (K:S)(i:Finset ι): (mat K).part (tile i)= (K i:ℂ):=by
 let f(j:ι):= (X).fire j; have he(A:Finset ι): Extra.Trajectories.Fits f A:= ⟨by intro i hi j hj h; exact Finset.disjoint_singleton.mpr h,mem_univ _⟩;
 have hp (A:Finset ι): Button.pose (R:=X) (fun i=> ⟨f i,Finset.singleton_nonempty i⟩) A=Poly.send (tile A) 1:= by
     rw [spar]; congr 1; apply Subtype.ext; change A.biUnion (fun i=>({i}:Finset ι)) = A; simp; exact he A
 unfold mat; rw [mapScores_apply,Poly.part_sum, sum_eq_single i]; · rw [Poly.part_smul, show (∏ j∈i, κ j)=_ from hp i,Poly.part_send,if_pos rfl,mul_one] -- change product sense
 · intro A _ h; rw [Poly.part_smul, show (∏ j∈A, κ j)=_ from hp A, Poly.part_send,if_neg (fun he=> h (congr_arg Subtype.val he.symm)),mul_zero]
 simp
lemma inked : Injective (mat (ι:=ι)):= fun u v h=> funext fun i=> Complex.ofReal_injective ((mat_reads u i).symm.trans ((congr_arg (fun j: Poly X=> j.part (tile i)) h).trans (mat_reads v i)))
lemma mat_one : mat (bench (∅:Finset ι) 1)=1:= by unfold mat; rw [mapBench]; simp
-- pointwise log.Snap.Ratio. Fakes zero coupling all nonzero.Don't emit as perturbative result.
def Earmark (K:Score ι)(m:ℕ): Score ι:= ∑ i∈range (m+1),tax i • stack (bench ∅ 1 - K) (i+1)
variable {m k i:ℕ}
lemma planting (K:S)(i:ℕ): mat (stack K i) = (mat K)^i := by induction i with
  | zero=> rw [stack,mat_one,pow_zero]
  | succ i ih=> rw [stack,pow_succ, show mat (comb 0 (stack K i) K)=_ from cap_combs (κ) (clicked (R:=X) _) (stack K i) K]; change mat (stack K i)*_= _; rw [ih]
lemma matTrans (K:S)(hm: n0 ≤ m)(h:K ∅=1) : connected (mat K)=mat (Earmark K m):= by
 let n:=Fintype.card ι; have hv:(mat K).part (X).quiet=1:= (mat_reads K ∅).trans (by rw [h]; simp); have he(i:ℕ)(hi:n< i):stack (bench ∅ 1 - K) i=0:= funext fun p=> struck _ (show ((bench ∅ 1 - K):Score ι) ∅=0 from (by rw [Pi.sub_apply,h,bench,if_pos rfl,sub_self])) p (lt_of_le_of_lt (card_le_univ p) hi); let f (t:ℕ):= tax t • stack (bench ∅ 1 - K) (t+1)
 have hz: Earmark K n= Earmark K m:= sum_subset (range_mono (by omega)) (fun i _ h=> by rw [he _ (by have := not_lt.mp (mt Finset.mem_range.mpr h); omega),smul_zero]); rw [← hz, log_formula hv, Earmark, mat]; unfold mat; rw [map_sum]; unfold unipotentLog; apply sum_congr rfl; intro i hi; rw [map_smul]; change _=(↑(tax i):ℂ) • mat (stack (bench ∅ 1 - K) (i+1)); rw [agreed, planting, show mat (bench ∅ 1-K)=mat (bench ∅ 1)-mat K from map_sub (mapScores _ (κ)) ..,mat_one]
lemma escalated (B:Book ι)(i:ℕ): knot B i 0= stack (B 0) i := by
 induction i with
 | zero=> rw [stack,knot,neutral,if_pos rfl]
 | succ i ih=> rw [stack,knot, pledge, show (_root_.Finset.HasAntidiagonal.antidiagonal (0:ℕ))={(0,0)} from (by ext ⟨x,y⟩; simp),sum_singleton]; rw [← ih]
lemma earnest (B:Book ι)(m:ℕ): connect m B 0= Earmark (B 0) m:= by unfold connect Earmark; simp only [Finset.sum_apply,Pi.smul_apply, escalated,Pi.sub_apply,neutral, if_true]
lemma tonal (u:ι→ℝ)(B:S): polish u (Earmark B m)= Earmark (polish u B) m:= by
 let v:Book ι:=fun _=> B; change polish u (Earmark (v 0) m)= Earmark (polishP u v 0) m; rw [← earnest,← earnest, ← hears]; rfl
-- any stencil.Test.Inflections.Syntax.t `jet`.
open GridRenewal.Rain
local notation "U"=> Ways ι
variable {f:Ways ι}{a:ℝ}
abbrev film (f:U): Ways ι:= fun i t=> Real.exp (f i t)
lemma hush (h:Paid (fun _:Unit=>f) a)(hh: f 0 ∅=0) (hm:n0 ≤ m): Switch.jet f=Earmark (Switch.jet (film f)) m:= by
 let x:=κ; let v:= film f; have he:= h.exponential; have hv: Switch.jet (film f) ∅=1:= (show Switch.jet (film f) ∅=film f 0 ∅ from Paid.atZero (fun _:Unit=>film f) he ∅ ()).trans (by unfold film; rw [hh,Real.exp_zero]); have hg : (mat (Switch.jet f)).part (X).quiet=0:= (mat_reads (Switch.jet f) ∅).trans (by rw [(Paid.atZero (fun _:Unit=>f) h ∅ ()),hh]; exact Complex.ofReal_zero); apply inked; rw [← matTrans _ hm hv, show mat (Switch.jet v) =cyclone (mat (Switch.jet f)) from soundExp x (clicked _ ) h, passes _ hg]; exact (connected_pass hg).symm
end YM.Qlocal.Canopy.Button
