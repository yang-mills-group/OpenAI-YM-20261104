import YM.GradedFar.Logged.Office
import YM.OPE.Eye.Fast

/-!
# (G.7) fixed clearance as well (on the physical Reader)
 Additional progress towards the OPE comparison.
-/
namespace YM.OPE.Logged.Unmoved
noncomputable section
open Function Filter MeasureTheory Set Orbits Spec
open Extraction OPE.Log Table Stroke Subtable Economy
open scoped Topology BigOperators Classical ContDiff
variable {I J L:Type} [Fintype I][Fintype J]
variable {G:Gauge}{C:Family G}{f: Extraction.Order}{S: Table C.book} (F: Final C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (U:LogTrace F R.port)
    (V: Services C f S)
variable {d:I→ℕ} {e:J→ℕ} {c M η:ℝ}(hc:0<c) (w:Labels S e)(v:Labels S d)
local notation "T"=> spectator F
local notation "Y"=> F.sector.derivatives
include hc V
lemma publication (z:C.book.Token)(w:J→C.book.Token) : ∃ C':ℝ, ∀ i:Viewers F, ∀ y:J→ E4,∀ o:E4,ClearOf o y c →
     ‖observe (T i) (beside (sole o) y) (beside (sole z) w)‖ ≤ C':= by
    classical
    by_contra! h; choose p t o hf hm using fun n:ℕ=> h (Real.exp (n:ℝ))
    let t' : ℕ→ℝ:= Nat.cast; have ht:Tendsto t' atTop atTop:=tendsto_natCast_atTop_atTop
    obtain ⟨hx,hp⟩:= free_clear ht hc (Eventually.of_forall hf)
    have hs:Kept atTop t' 0 (fun i=>sole (o i)):= fun b hb=> Eventually.of_forall fun i j j' h=>(h (Subsingleton.elim ..)).elim
    obtain ⟨n,hn⟩:= (viewer_cost F V.schedule (sole z) w ht p hs hx hp le_rfl le_rfl 1 (by ring_nf; norm_num)).exists
    rw [one_mul] at hn; exact (hm n).not_ge hn

variable (p:Economy.Small L) (s:L→Viewers F)(h:ℕ) (x:L→I→E4)(z:L→E4)(y:L→J→E4)(hm:0 ≤ M)(hη:0<η)
  (hx:∀ᶠ i in p.p, WithinRoom (p.r i) M η (x i) (z i))(hy:∀ᶠ i in p.p,ClearOf (z i) (y i) c)
include U hy
lemma their (v:S.Field h) : Paint p (fun _=>1) (fun i=> upon (T (s i)) h (z i) (y i) w v) := by
   let x : Labels S (fun _:Unit=>h) := fun _=> v
   obtain ⟨C',hh⟩:= publication (J:=J) F V hc (Orbits.names x ()) (Orbits.names w)
   refine Paint.bounded C' (hy.mono (fun i h'=>?_)); change ‖whole _ _ _ _ _‖ ≤ _
   rw [whole_observed]; exact hh (s i) _ _ h'
lemma theirs {P:L→ℝ} (u:L→S.Field h)(hP:Paint p P u): Paint p P (fun i=> upon (T (s i)) h (z i) (y i) w (u i)) := by
    let M:=Module.finBasis ℂ (S.Field h); let D j i:= M.coord j (u i) • upon (T (s i)) h (z i) (y i) w (M j)
    have he(i:L): upon (T (s i)) h (z i) (y i) w (u i)= ∑ j,D j i:= by
       conv_lhs => arg 2; rw [← M.sum_repr (u i)]
       rw [map_sum]; exact Finset.sum_congr rfl fun j _=> map_smul (upon (spectator F (s i)) h (z i) (y i) w) _ (M j)
    simp_rw [he]; apply Paint.sum; intro i h; simpa only [mul_one, Function.comp_def] using (their F R U V hc w p s _ z y hy (M i)).scales (Paint.linear_c (M.coord i) hP)
-- combine old shadow residual and shadow→packet on poses, fixed labels
abbrev rate (w:Labels S e)(v:Labels S d)(s:Viewers F)(h:ℕ)(x:I→E4)(z:E4)(y:J→E4) :=
    whole (T s) x v y w-upon (T s) h z y w (R.packet h x v z)
include hm hη hx
lemma depart : Paint p (Stroke.lifetime d h ∘ p.r)
    (fun i=>rate F R w v (s i) h (x i) (z i) (y i)) := by
    have hb := Trace.shadow_pair F R p hm hη x z hx U v h
    have hi := theirs F R U V hc w p s h z y hy _ hb
    have hp:=(Stroke.orders_far F R p hm hη x z hx U v s h y hc hy (e:=e)).2 w
    refine (hp.minus hi).assists (Eventually.of_forall fun i=>?_); unfold rate discrepancy; rw [map_sub]; abel
variable {w v}
lemma nonlinear {v:L→Labels S d} {w:L→Labels S e} (hv:∀ i,Paint p (fun _=>1) (fun s=>v s i))(hw:∀ i,Paint p (fun _=>1) (fun s=>w s i)) :
    Paint p (Stroke.lifetime d h ∘ p.r) (fun i=> rate F R (w i) (v i) (s i) h (x i) (z i) (y i)) := by
   let D i:= Orbits.moment (T (s i)) (S:=S) (d:=Sum.elim d e) (beside (x i) (y i)) - packetM F R (s i) h (z i) (x i) (y i) d e
   have hc i v w : D i (stages v w)=rate F R w v (s i) h (x i) (z i) (y i) := by unfold D; rw [MultilinearMap.sub_apply, booked]; rfl
   have he (u:Labels S (Sum.elim d e)) : Paint p (lifetime d h ∘ p.r) (fun i=>D i u) := by
      let v':Labels S d:=fun j=>u (.inl j); let w':Labels S e:=fun j=>u (.inr j)
      rw [show u=stages v' w' from funext fun j=>by cases j <;>rfl]; simp_rw [hc]; exact depart F R U V ‹0<c› w' v' p s h x z y hm hη hx hy
   have hA (j:I⊕J) : Paint p (fun _=>1) (fun i=> stages (v i) (w i) j) := by cases j with| inl i=> exact hv i| inr j=> exact hw j
   simp_rw [← hc]; simpa only [Finset.prod_const_one,one_mul] using Paint.contract D he (fun _ _=>1) (fun i=>stages (v i) (w i)) hA
-- fresh result
omit V hc hy
lemma selected {v:L→Labels S d}(hv:∀ i,Paint p (fun _=>1) (fun s=>v s i)) :
    Paint p (Trace.core d h ∘ p.r) (fun i=>R.fresh h (x i) (z i) (v i)) := by
    have he u:=Trace.current F R p hm hη x z hx U u h (d:=d)
    simpa only [Finset.prod_const_one,one_mul] using Paint.contract _ he (fun _ _=>1) v hv
lemma scored {v:L→Labels S d}(hv:∀ i,Paint p (fun _=>1) (fun s=>v s i))(u:R.channels h):
    Paint p (Trace.core d h ∘ p.r) (fun i=> R.coef h u (x i) (v i) (z i)) := by
    let f:=fun i=> (⟨R.fresh h (x i) (z i) (v i),R.fresh_mem _ _ _ _⟩:R.stratum h)
    have he:=selected F R U p h x z hm hη hx hv; have hx: Paint p _ f:= he.of_le (Eventually.of_forall (fun i=> le_refl ‖f i‖))
    exact Paint.linear_c ((R.basis h).coord u) hx
end
end YM.OPE.Logged.Unmoved
