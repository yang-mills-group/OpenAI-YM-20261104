import YM.MS.Graphical.PricePin
import YM.MS.Graphical.OneRoot

/-!
# UV price and finite parts on multiple pins

Assemble pages first (including all their CTs), keep open axes. Package loop
and sewing estimates with existence of a common-radius and all-times
representative. `regularPart` is only to be applied on schedules where the
limit exists after this assembly; e.g. separated graphs in `ManyRoot.lean`.
`integral_payment` checks specialization can then pass through multi-pin UV
integrals with no extra CT.
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval
variable {I : Type} {t v u w a R : ℝ} {m n : ℕ} {q k j : ℤ} {G : Gauge} {x : Tone.QP}
variable {F H X Y : Schedule G} {z : ℂ} {b c : Bool}

namespace PinPrice
lemma closeT (h : PinPrice true R q F) (hs : Short R) (y : ℝ) : PinPrice true R (q-2) (closeAt y F) := by
  refine ⟨ h.1.close hs y, show InPins _ _ from fun b=>?_⟩
  convert Pays.close F ((show InPins R F from h.2) (b+2)) hs.2.1 hs.2.2 y h.1.fine using 1 <;> first| rfl | ring
lemma weak (h : PinPrice b R q F) : Subponential R F:= by
  cases b; exact h.2; exact ⟨0,(show InPins R F from h.2) 0⟩
lemma treeT (h : PinPrice b R q F) (he : PinPrice true R k H) :
    PinPrice true R (q+k-2) (treeAt F H) := by
  obtain ⟨a,ha⟩:=weak h
  refine ⟨ h.1.tree he.1,show InPins _ _ from fun b=>?_⟩
  convert ha.attach ((show InPins R H from he.2) (b-4-a)) using 1 <;> first| rfl | ring
lemma joinT (h : PinPrice b R q F) (he : PinPrice c R k H) (hs : Short R) (x : Tone.QP) (hx : x≠ 0)
    (y : ℝ) : PinPrice true R (q+k-2) (joinAt x y F H) := by
  obtain ⟨a,ha⟩:=weak h; obtain ⟨b,hb⟩:= weak he
  exact ⟨AtPin.joined x y h.1 he.1 hs,ha.joins hb hs.2.1 hs.2.2 y h.1.fine he.1.fine x hx⟩
lemma top (h : PinPrice true R q F) : PinPrice true R q (integratePins F) := by
  obtain ht: InPins R F:= h.2
  refine ⟨ h.1.integrated (ht 1) zero_lt_one, show InPins _ _ from fun b=>?_⟩
  exact (integrate_pay (ht (max 1 b)) (lt_max_of_lt_left zero_lt_one) h.1.borel).more (le_max_right ..)
end PinPrice
namespace Countered
lemma closeT (h : Countered true q F) (y : ℝ) : Countered true (q-2) (closeAt y F) := by
  obtain ⟨R,X,hR,H,hX⟩:= h; exact ⟨R,_,hR,H.close _ y,PinPrice.closeT hX hR y⟩
lemma treeT (h : Countered b q F) (he : Countered true k H) : Countered true (q+k-2) (treeAt F H) := by
  obtain ⟨R,X,Y,hR,hX,hY,h,hp⟩:= static2 h he; exact ⟨R,_,hR,hX.tree hY,PinPrice.treeT h hp⟩
lemma joinT (h : Countered b q F) (he : Countered c k H) (x : Tone.QP) (hx : x≠0) (y : ℝ) :
    Countered true (q+k-2) (joinAt x y F H) := by
  obtain ⟨R,X,Y,hR,hX,hY,h,hp⟩:= static2 h he; exact ⟨R,_,hR,hX.joins x y hY,PinPrice.joinT h hp hR x hx y⟩
lemma top (h : Countered true q F) : Countered true q (integratePins F) := by
  obtain ⟨R,X,hR,H,hX⟩:= h; exact ⟨R,_,hR,H.integrate,PinPrice.top hX⟩
lemma weak (h : Countered b q F) : Countered false q F:= by
  obtain ⟨R,X,hR,H,hX⟩:= h; exact ⟨R,X,hR,H,hX.1,PinPrice.weak hX⟩
lemma sum (S : Finset I) {F : I→ Schedule G} (H : ∀ i∈S, Countered b q (F i)) : Countered b q (∑ i∈S,F i) := by
  classical induction S using Finset.induction with
  | empty=>rw [Finset.sum_empty]; exact zero' ..
  | insert i u hi ih=> rw [Finset.sum_insert hi]; exact (H i (by simp)).add (ih fun j hj=> H j (Finset.mem_insert_of_mem hj))

-- applied integral law, even on the actual punctured input representatives (all scales)
theorem cutRemoves (h : Countered true q F) :
    ∀ᶠ z in dotty, ∀ t : ℝ, (Gather (fun s=>F s z) t) ∧ ∀ m, ∀ w : Legs (Shore G m),
      Tendsto (fun p:ℝ=>∫ i in p..t, F i z m w) atBot  (𝓝 (integratePins F t z m w)) := by
  obtain ⟨R,X,hR,H,A,hX⟩:= h
  filter_upwards [H,H.integrate,dotty_bill hR.1] with i hi hh hD
  have hp : InPins R X:= hX; intro t; simp_rw [hi,hh]
  exact ⟨pinGather (hp 1) zero_lt_one A.borel hD _,fun _ w=> integral_from_UV (hp 1) zero_lt_one A.borel hD w _ ⟩
theorem everyForm (h : Countered b q F) : ∀ᶠ z in dotty, ∀ t,Form0 false (F t z):= by
  obtain ⟨R,X,hR,H,A,hX⟩:=h; filter_upwards [H,dotty_bill hR.1] with i hi hp; simp_rw [hi]; exact fun t=> A.fine t _ hp
end Countered


lemma fromLimit (F : Schedule G) {X : Mob G} (h : Lift (F t) X): regularPart F t=X:= by
  funext m w; exact (Lift.wind h m w).limUnder_eq

lemma reg_is (h : PinPrice b R q F) (hv : Short R) (Hq : TimeEq X F) (t : ℝ) : regularPart X t= F t 0:=
  fromLimit X (h.1.Lift Hq hv.1 _)
lemma Countered.limit (h : Countered b q F) (t : ℝ): Lift (F t) (regularPart F t):= by
  obtain ⟨R,X,hR,H,hX⟩:= h; rw [reg_is hX hR H t]; exact hX.1.Lift H hR.1 t
lemma Countered.foot (h : Countered b q F) (t : ℝ): Issue q (regularPart F t) ∧ Form0 false (regularPart F t):= by
  obtain ⟨R,X,hR,H,hX⟩:=h; rw [reg_is hX hR H t]; exact ⟨hX.1.capacity t 0 (mem_ball_self hR.1),hX.1.fine t 0 (mem_ball_self hR.1)⟩
lemma Countered.trains (h : Countered true q F) : ∀ t:ℝ, Gather (regularPart F) t := by
  obtain ⟨R,X,hR,H,hX⟩:=h; rw [funext (reg_is hX hR H)]; exact pinGather ((show InPins R X from hX.2) 1) zero_lt_one hX.1.borel (mem_ball_self hR.1)
lemma sum_progress (h : Countered b q F) (hp : Countered c k H) : regularPart (F+H) = regularPart F + regularPart H:=
  funext fun t => fromLimit _ (Lift.add (h.limit t) (hp.limit t))
lemma regularPart_zero : regularPart (0:Schedule G)=0:= funext fun _=> fromLimit _ Lift.zero
lemma sum_payment (S : Finset I) {F : I→Schedule G} (h : ∀ i∈S, Countered b q (F i)) :
    regularPart (∑ i∈S,F i) = ∑ i∈S,regularPart (F i) := by
  classical
  induction S using Finset.induction with
  | empty=> simp [regularPart_zero]
  | insert i s hi ih=>
    obtain hv: ∀ j∈s, Countered b q (F j) := fun _ hj=> h _ (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi,Finset.sum_insert hi,sum_progress (h i (by simp)) (Countered.sum s hv),ih hv]
lemma close_payment (h : Countered true q F) (y t : ℝ) : regularPart (closeAt y F) t =
    radialClose (halfD t) 0 y (regularPart F t):= by
  obtain ⟨R,X,hR,H,hX⟩:= h; rw [reg_is (PinPrice.closeT hX hR y) hR (H.close _ y),reg_is hX hR H]; rfl
lemma join_payment (h : Countered b q F) (hp : Countered c k H) (x : Tone.QP) (hx : x≠0) (y t : ℝ) :
    regularPart (joinAt x y F H) t = wickJoin x (halfD t) 0 y (regularPart F t) (regularPart H t) := by
  obtain ⟨R,X,Y,hR,hX,hY,h,hp⟩:= Countered.static2 h hp; rw [reg_is (PinPrice.joinT h hp hR x hx y) hR (hX.joins x y hY), reg_is h hR hX, reg_is hp hR hY]; rfl
lemma tree_payment (h : Countered b q F) (hp : Countered true k H) :
    regularPart (treeAt F H) t = bridging t (regularPart F t) (regularPart H t) := by
  obtain ⟨R,X,Y,hR,hX,hY,h,hp⟩:= Countered.static2 h hp; rw [reg_is (PinPrice.treeT h hp) hR (hX.tree hY), reg_is h hR hX,reg_is hp hR hY]; rfl
lemma integral_payment (h : Countered true q F) : regularPart (integratePins F) t = mend (regularPart F) t := by
  obtain ⟨R,X,hR,H,hX⟩:= h; rw [reg_is (PinPrice.top hX) hR H.integrate, funext (reg_is hX hR H)] ; rfl
lemma Countered.runsOut (h : Countered b q F) (hq : q <0) : TimeEq F 0∧ regularPart F=0:= by
  refine ⟨?_,funext fun t=> funext fun m=>funext fun l=> (h.foot t).1 m l (by omega)⟩
  obtain ⟨R,X,hR,H,hX⟩:=h; refine TimeEq.trans' H ?_
  unfold TimeEq; filter_upwards [dotty_bill hR.1] with z hz; intro t; exact funext fun m=> funext fun l=> hX.1.capacity t z hz m l (by omega)
end YM.MS.Graphical
