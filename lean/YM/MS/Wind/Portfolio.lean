import YM.MS.Wind.Clone
/-!
# The all-order High UV solution from the lattice side

Producing Taylor match, contingent only on the results of the continuum calculation.
 Later instantiate the `Disc` assumptions using MS. Leading order agreement follows from
 a *continuum only* test, no regulator or scheme equality assumed (Lie token).
 Should specialize Leading for order0 mark basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting Knobs Local.Physical
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge} {U:ℕ→Type}{p q:Team}{φ φ':Actor G}{F H V: Dec G}{b:Bool}{k r d:ℕ}{l:List (Lane4 G)}{u:ℤ}
-- Knobs mapping

def Key (G:Gauge) : Knobs (fun _=> Plan) G where
   wake p:= col (skyline G p)
   stay p q i h := by funext y; unfold col; rw [step_birth (k:=i+1) (skyPC G p) (skyPC G q) (fun j hj=>h j (by omega)) _ (by omega)]
variable {B:Deck G}(W: LitBook B)
def Seek (W: LitBook B)(p:Team)(d:ℕ): Knobs (fun _=> Tact B d) G where
   wake A:= col (horizon W p A)
   stay A C i h:= by funext y; unfold col; rw [money_before W A C (k:=i+1) (fun j hj=>h j (by omega)) _ (by omega)]
lemma rewind {K:Knobs U G}{hp hq: Code U} {H':ℝ→Law G}{Z Z':Pack G}
 (hK:K.wake hp k=fun i=> Z i.1 (exp i.2)) (hL:K.wake hq k=fun i=> Z' i.1 (exp i.2))(h:∀ i<k,hp i=hq i)(hf:∀ i,TouchF (Z i))(hg:∀ i, TouchF (Z' i))(hh:Knick Z Z' r u b H'): Move b K hp hq k r u H':= by
    refine ⟨⟨h, fun i hi t v ht hv=>?_⟩,fun y t w hp hx j he=>?_⟩
    · rw [hK,hL]; exact sub_eq_zero.mp ((hh.size t.1) (exp t.2) v (by omega))
    rw [hK,hL]; obtain hu:= hh.pay y (exp t) w hp hx j he; rw [Pi.sub_apply, Pi.sub_apply, torch_sub _ ((hf y).routine _ _) ((hg y).routine _ _)] at hu; linear_combination (norm:=abel) - hu
lemma first_top (h:PC G p F)(x:ℝ):
    Rank (F 1 x) 3∧∀ t, Book.mask 3 (F 1 x t)= Menus.Top G:= by
   have he : Near false (F 1 x) := by obtain ⟨n,hx⟩:= (h.owes 1).pay; refine ⟨((h.owes 1).stay x).joint,⟨n,hx x⟩,?_⟩; intro t i _; obtain ht := (h.recu 1 (by omega) x).2 t i; simpa only [Pi.add_apply,path,Domain.paths,Finset.Ico_self,Finset.sum_empty,smul_zero,Pi.zero_apply, add_zero] using ht
   have hP : F 1 x 0=run (style G p x 1):= (h.recu 1 (by omega) x).1; obtain ⟨hs,H'⟩:= Dprecise he (r:=3) (by rw [hP]; exact Tone.oneRank (style_limit p x G 1))
   refine ⟨hs,fun t=>?_⟩; ext l; by_cases ht:(l.length:ℤ)=3
   · rw [enough _ ht, H' l ht,hP, ← Top_P p x,enough _ ht]
   rw [strange _ ht]; exact Eq.symm (strange _ ht)
lemma mark_seek (h: G.Simple): Marked (Seek W p d) (col (skyline G p)) B d where
    law A:= PMSolve h (skyPC G p) (aqua W p A) (decor W p A) (fun x=> law W p x A h)
    occurs A:= post_ok _ (aqua W p A).owes
    moves A i r v hv ht a b hp hq hk hK:= by
       obtain ⟨Q,X,H1,H2,H⟩:= room_here (n:=i) W p A hv ht hp hq hk hK; exact ⟨_,rewind (K:=Seek W p d) (hp:=A) (hq:=Menus.patch A Q X i) rfl rfl H.past (fun x=>(((aqua W p A).owes i).stay x).joint) (fun x=> (((aqua W p _).owes i).stay x).joint) (mark_pay W H)⟩
-- meet point target independent first normalized. Only *Equals* on own dimension, token gauge symmetry from proof. No off-shell normalization assumptions.
def Compact (Q:Recount G): Prop:= ∃ F,Class (G:=G) F 4 ∧ (∀ i j k,Mark.token F i j k=(Mark.LieColor i j k:ℂ))∧ (∀ (x:Clock ℝ), EqualAt 3 (Q 1 x) F)
lemma action_seek (h:G.Simple){Q:Recount G}(hs:Compact Q): Tuning (Key G) Q (Menus.LE G 4) where
    commute p:= SatSolve h (skyPC G p)
    rates p:= post_ok _ (skyPC G p).owes
    stamp:= ⟨1,one_ne_zero, Top_class h (bulk_three h),fun i j k=> by rw [Complex.ofReal_one, mul_one]; exact token_R ..⟩
    jump n i f hf p:= by obtain ⟨q,hq⟩:= buys_cube p h i hf; exact ⟨q,rewind (K:=Key G) (hp:=p) (hq:=q) rfl rfl hq.past (fun x=> ((skyPC G p).owes n|>.stay x).joint) (fun x=> ((skyPC G q).owes n|>.stay x).joint) (bulk_pay (skyPC G p) (skyPC G q) hq i.le)⟩
    scale n i a b ha hb p:= by obtain ⟨q,hq⟩:= buys_pair (G:=G) p i ha hb; exact ⟨q,rewind (K:=Key G) (hp:=p) (hq:=q) rfl rfl hq.past (fun x=> ((skyPC G p).owes n|>.stay x).joint) (fun x=> ((skyPC G q).owes n|>.stay x).joint) (bulk_pay (skyPC G p) (skyPC G q) hq i)⟩
    leads p x w he hw j hJ:= by
       obtain ⟨F,ha,hT,h'⟩:=hs; let L:=Key G|>.wake p 1 x; have ht (i:ℝ): F (sail (ray w) i)= Q 1 x (sail (ray w) i):= Eq.symm (h' x _ (sail_course i (ray_course (w:=w) (b:=true) fun _=>he) rfl) (by simp [hw]));
       have hp : torch j L w = torch j (Top G) w:= by unfold torch; rw [show fieldVal L (ray w)=_ from ?_]; funext k; unfold fieldVal; rw [← (first_top (skyPC G p) x.1).2 (exp x.2), enough _ (by simp [hw])]; rfl
       rw [show torch j _ w= _ from hp, face_here (bulk_three h) (w:=w) (fun _=>he) _ hJ, torch_at j (Q 1 x) w,show (fun k:ℝ=> Q 1 x _ )= fieldVal F (ray w) from funext fun t=> (ht t).symm]; rw [show reading j _= _ from (ha.graded.const_term w (fun _=>he) (j:=j))]; rw [top_align h ha (fun i j k=>(hT i j k).trans (token_R ..).symm) w he hw]

-- verified Taylor regulator comparison, given just appropriate continuum quantities. Signs are our conventions. Known not enough at separated position or for rank-correlation.
theorem portH (h:G.Simple){R:Recount G}(H:Disc true 1 R R ((2:ℂ)⁻¹) 4)(ht: Compact R): ∃ p:Team, Fixed (col (skyline G p)) R true 4 1 := High.action h H (action_seek h ht) (fun _=> ⟨0,0,0⟩)
theorem marksAt (h:G.Simple){R S:Recount G} (HQ:Fixed (col (skyline G p)) R true 4 1) (HS:Disc false 0 R S 1 d) : ∃ A:Acts B d, Fixed (col (horizon W p A)) S false d 0:= High.mark (k:=Seek W p d) HQ HS (by omega) (mark_seek W h) (0:Acts B d)
end YM.MS.Wind
