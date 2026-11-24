import YM.FormalBulk08.Sound.Officers

set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Sound
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries UVExtension UVExtension.Free Matrix Exterior Tree North
open Dawn Kemp Drift Quire Elm Pose
open scoped Topology ENNReal BigOperators Classical Matrix ContDiff
variable {G:Gauge}{I J: Type}{K:KernelChoices}{ρ:ChartRatio G}{W:Lab G K I}{E d j t e r D:ℕ}
variable (x:Leaf W.scrolls)(a:hue G)(o:Loc G 1)(hp:Use W ρ E) (h:LocalRatio ρ)(hs:G.Simple)
lemma strip_flag {V I:Type*}[Fintype V][DecidableEq V] (H:Hull V I)(p q U Z:Pap (V⊕I))(h:Solved H p)(hp:Through E p q)(he:Through E U Z) : Through E (flag H p U) (flag H q Z):= by
   obtain ⟨hv,hq⟩:= solved_change H p q h hp; have hh:= hq.expan_congr (plur H p h); have hy : Through E (vocal H p) (vocal H q):= beam_through _ hh; unfold flag; refine ((?_ : Through E (-(covelog (vocal H p))) (-(covelog (vocal H q)))).expan_congr (by rw [map_neg,covelog_rank (voice H p h),neg_zero])).mul (beam_through _ (hh.mul (Through.change_congr _ he)))
   intro j hj; rw [map_neg,map_neg]; exact congr_arg Neg.neg (Through.cove_congr hy (voice H p h) _ hj)
abbrev Qpatch := destination (W.V x.a) x.b x.b
def ferryFlag (n:Side)(k:(boxS x n).Choices)(T:Pot G) (Y: Anthem D G)(l d:ℕ)(p:Studio D):=
    PowerSeries.C (MvPolynomial.C (aven (Qpatch x).L d))* ∑ i:Site (Qpatch x).L, flag (hospital x n hp) (joy (ρ:=ρ) x n T k) (Shaw x n (stepsong (Qpatch x) Y (growL _ _) p i) l)
include h hs
lemma standUp (n:Side)(k:(boxS x n).Choices)(Y: Anthem D G)(l d:ℕ)(p:Studio D) :
    let T:=heir a ρ W x.a (x.b+1)
    Through E (ferryFlag x hp n k T Y l d p) (ferryFlag x hp n k (stopper T E) (sliceM Y E) l d p):= by
   intro T; unfold ferryFlag; refine (Through.exact_eq _ _).mul (Through.finsetSum ?_)
   intro i _
   let P:=Qpatch x; let q(R:Anthem D G):= stepsong P R (growL _ _) p i
   refine strip_flag (hospital x n hp) _ _ _ _ (bedded x n hp a h hs k) (stir_ink x T (stopper T E) E (fun j hj=>(if_pos hj).symm) _ k) ?_; unfold Shaw Reef.seat; refine Through.change_congr _ (Through.map_left _ ?_)
   intro j hj; have ht: q (sliceM Y E) j=q Y j:= by unfold q stepsong Kemp.work sliceM stopper; simp_rw [if_pos hj]
   simp only [Kemp.banner,coeff_mk]; change (∑ i∈Finset.range _, facade i (sieve _ (q Y j i)))=∑ i∈Finset.range _, facade i (sieve _ (q _ j i));rw [ht]
lemma hatched (k:∀ n:Side,(boxS x n).Choices)(Y: Anthem D G)(l d:ℕ)(p:Studio D) (he: e≤ E)(r:ℕ) (hY: Wade o (sliceM Y E) l)(hy:∀ p e r,∃ A, Knoxville (fame _) (W.windowU x) (0,o) (sliceM Y E p e r) A) :
   let T:=heir a ρ W x.a (x.b+1)
   Kalm (W.windowD x) (0,o) (quickHat ρ x d l T Y p e r) (fun n=> rancho (ferryFlag x hp n (k n) T Y l d p) e r):= by
   intro T; let V:=stopper T E; let S:=sliceM Y E; let P:=Qpatch x;let U i:= stepsong P S (growL _ _) p i; have hp': Vivid V:= North.born a (North.porch x) hp h hs; have hz(x: Site P.L):=step_can o P S hY (growL _ _) p x;have hX(x: Site P.L):=step_agate o P S hY (growL _ _) p x
   simp_rw [show ∀ n,rancho (ferryFlag x hp n (k n) T Y l d p) e r= rancho (ferryFlag x hp n (k n) V S l d p) e r from fun n=>congr_arg (marble r) ((standUp x a hp h hs _ _ Y l d p) e he)]
   rw [Drift.quo_eq x d l T V Y S (fun j hj=> (if_pos hj).symm) (fun p j hj=>(if_pos hj).symm) p ρ e r he]
   have he1 (n):Solved (hospital x n hp) (joy x n V (k n) (ρ:=ρ)):= (solved_change _ _ _ (bedded x n hp a h hs (k n)) (stir_ink x T V E (fun j hj=>(if_pos hj).symm) _ _)).1
   have he2 n: rancho (ferryFlag x hp n (k n) V S l d p) e r= aven P.L d • ∑ i:Site P.L, rancho (flag (hospital x n hp) (joy (ρ:=ρ) x n V (k n)) (Shaw x n (U i) l)) e r:= by
       unfold ferryFlag rancho; simp_rw [←canyon_eq,coeff_C_mul,map_sum,show ∀ a:ℝ,∀ g:TypeR (wire G n),MvPolynomial.C a*g=a • g from fun a g=> by rw [MvPolynomial.smul_eq_C_mul]];rw [map_smul,map_sum] -- hm map_sum
   simp_rw [he2, show ∀ n i,rancho (flag (hospital x n hp) (joy (ρ:=ρ) x n V (k n)) (Shaw x n (U i) l)) e r=_ from fun n i=> support_flag x hp n V (U i) l (k n) h (hz i) (hX i) hp' (he1 n)]
   unfold quickHat; apply Kalm.smul; apply kalm_many _; intro i _;apply kalm_many _; intro b _
   have hP j r:∃ B,Knoxville (fame _) (W.windowU x) (lift i,o) (U i j r) B:= by
       obtain ⟨C,hC⟩:=hy (Dawn.throughW i _ (growL _ _) p) j r
       refine ⟨C,?_⟩; have ht:= mantle_pay (lift i) hC;rw [show Lotus.tint (lift i) (show edgeL G from (0,o))=(lift i,o) from Prod.ext (zero_add _) rfl] at ht; exact ht
   have hx:= certify x o hp V (U i) hp' (hz i) (hX i) (spineBudget x a hp h hs) h (lift i,o) k hP b e r
   have ht:= kalm_cut hx
   exact chief_h o P i ▸ ht
end YM.FormalBulk08.Sound
