import YM.FormalBulk08.Sound.Hatch

/-! Salvo grades in chain at/infinite limit. Equivalent recipe uses
 `stopper` on Level E only; any other values above ignored.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Sound
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries UVExtension UVExtension.Free Matrix Exterior Tree North
open scoped Topology ENNReal BigOperators Classical Matrix
variable {G:Gauge}{I J: Type}{K:KernelChoices}{ρ:ChartRatio G}{W:Lab G K I}{E d j t:ℕ}
variable (x:Leaf W.scrolls)(a:hue G)(hp:Use W ρ E) (h:LocalRatio ρ)(hs:G.Simple)
lemma stir_ink (Y Z:Pot G)(e:ℕ)(p:∀ i≤ e,Y i=Z i)(n:Side)(k:(boxS x n).Choices): Through e (joy (ρ:=ρ) x n Y k) (joy x n Z k (ρ:=ρ)) := by
    unfold joy flush vacuumU; apply Through.add _ (Through.exact_eq _ _); apply Through.change_congr; refine ((Through.map_left _ ?_).sub (Through.exact_eq _ _))
    intro j hj; simp_rw [sow_coeff,sow,p j hj]
lemma solved_change {V I:Type*}[Fintype V][DecidableEq V] (H:Hull V I)(p q:Pap (V⊕I))(h:Solved H p)(he:Through E p q):
    Solved H q ∧ Through E (positive H p) (positive H q) := by
   have hv: Through E (toInk H p) (toInk H q):= Through.change_congr _ he
   exact ⟨(hv 0 (Nat.zero_le _)).symm.trans h, (hv.sub (Through.exact_eq _ _)).sub (Through.exact_eq _ _)⟩
lemma through_strip {V I: Type*}[Fintype V][DecidableEq V] (H:Hull V I)(p q:Pap (V⊕I))(h:Solved H p)(he: Through E p q): Through E (out H p) (out H q):= by
    obtain ⟨hy,hq⟩:= solved_change H p q h he; have ht:Through E (vocal H p) (vocal H q):= beam_through _ (hq.expan_congr (plur H p h)); exact (Through.exact_eq _ _).add (Through.cove_congr ht (voice H p h))
include hp h hs
lemma spineBudget :
    ∀ e r,∃ B:ℝ,Bail (fame _) (W.windowU x) (stopper (heir a ρ W x.a (x.b+1)) E e r) B:= by
    intro e r; by_cases he:e≤E
    · rw [show stopper _ E e= _ from (if_pos he : stopper (heir a ρ W x.a (x.b+1)) E e= _)]
      obtain ⟨B,u,w,H⟩:= diadem a hp h hs he r;exact ⟨_,(H (North.porch x)).1⟩
    rw [stopper,if_neg he]; exact ⟨0,bail_void ..⟩
lemma at_limit (e r:ℕ)(p:e ≤ E)(y:Fin r)(k:(n:Side)→(boxS x n).Choices):
      let T:=heir a ρ W x.a (x.b+1)
      Kith (W.windowD x) (crest ρ a x T e r) (fun n=> rancho (unwashed x n hp (k n) T) e r):= by
   intro T; let Y:=heir a ρ W x.a x.b; have hB:= born a (North.porch x) hp h hs
   cases e with
   | zero=>
       unfold crest; rw [if_pos rfl]; simp_rw [unwashed,rancho,out_main (hospital x _ hp) (joy _ _ T _) (bedded x _ hp a h hs _)]
       let V:=stopper Y E; have he:V 0=Y 0:= if_pos (Nat.zero_le E); let U:=W.windowD x
       have hH:=born a x hp h hs
       obtain ⟨C,c,Z,H⟩:= diadem a hp h hs (Nat.zero_le E) r
       have hW n: marble r ((hospital x n hp).main) = cum y n (V 0 r):= by
            rw [show (hospital x n hp).main=coeff 0 (stone Y n) from (heir_zero x hp a h hs n).symm,← stopper_presents (T:=Y) (Nat.zero_le E)]; exact hH.flower 0 r y n
       simp_rw [hW]; change Kith _ (Y 0 r) _;rw [←he]; exact stable (hp.zero _).le (hH.civil 0 r) (show Bail (fame _) _ (V 0 r) (C x) from (by rw [he]; exact (H x).1)) y
   | succ e=>
       unfold crest; rw [if_neg (show ¬_= _ by omega),if_neg (show ¬r=0 by have :=y.isLt;omega)]
       let U:=stopper T E; have hy(n): Through E (joy x n T (ρ:=ρ) (k n)) (joy x n U (ρ:=ρ) (k n)):= stir_ink x T U E (fun j hj=> Eq.symm (if_pos hj)) _ _
       have hT (n):=bedded x n hp a h hs (k n)
       have hc(n):Solved (hospital x n hp) (joy x n U (k n)):= (solved_change _ _ _ (hT n) (hy n)).1
       have hh n: rancho (unwashed x n hp (k n) T) (e+1) r = rancho (unwashed x n hp (k n) U) (e+1) r:= congr_arg (marble r) (through_strip (hospital x n hp) _ _ (hT n) (hy n) _ p)
       rw [camps x T U (fun j hj=>(show U j=T j from if_pos (hj.trans p)).symm)]; simp_rw [hh,striker x _ U hp h hB _ (hc _)]; unfold obs; exact kith_many _ fun i _=> cast_curve x hp k hB h (spineBudget x a hp h hs) _ i _ y
end YM.FormalBulk08.Sound
