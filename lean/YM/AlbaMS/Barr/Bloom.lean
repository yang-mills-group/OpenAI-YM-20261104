import YM.AlbaMS.Barr.Berries
/-!
# acyclic projection using one Landau choice

Legitimate only at pin where ∂g invertible ghost laplacian. Not used on bulk jet
(Z or U). Useful for linear gauges comparisons. Does not identify lifts merely
by master assumptions. Need prove conjugation equality before transporting. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix
variable {E R : Type*}[CommRing R][Algebra ℚ R]{ρ:E→Bool}{d: E→E→R}{U S : Coil ρ R}{b:Bool}{s:Finset E}
lemma FinRank.withering (h:FinRank U): FinRank (wither d s U):=⟨_, h.choose_spec.withers⟩
lemma felled (h: Tone b U)(H:Graded ρ false d)(hp:FinRank U): Tone b (wither d s U):=by
  obtain ⟨n,hp⟩:=hp; rw [withers hp (by omega : n≤2*n),twig_apply]; refine Tone.sum _ _ fun i _=>?_ ; rw [pe_apply]; apply Tone.smul; rename_i hi; clear hi; induction i with|zero=>exact h|succ i ih=> rw [pow_succ', Module.End.mul_apply]; have he:= touch_tone _ _ _ _ s ih H; simpa using he -- types
lemma foe (h:FinRank U)(H:FinRank S): wither d s (U-S)=wither d s U-wither d s S:=by
  rw [sub_eq_add_neg U S,wither_add h H.neg, ← neg_one_smul R S,wither_smul H, neg_one_smul, sub_eq_add_neg]
omit [Algebra ℚ R] in
lemma negativeGrade (h:Graded ρ b d): Graded ρ b (-d):= fun i j he=> h i j fun ha=> he (by simp [ha])
lemma backfit (h:Graded ρ false d)(ht:FinRank U): wither d s (wither (-d) s U)=U:=by rw [← composition h (negativeGrade h) ht,add_neg_cancel,wither_empty ht]
lemma liftFit (h:Graded ρ false d)(ht:FinRank U): wither (-d) s (wither d s U)=U:=by rw [← composition (negativeGrade h) h ht,neg_add_cancel,wither_empty ht]
lemma stoked (h:Graded ρ false d)(ht:FinRank U)(he:FinRank S)(hl:wither d s S=wither d s U): S=U := by rw [← liftFit (s:=s) h he,hl,liftFit h ht]
end YM.MSBar.Bric.Coil
namespace YM.MSBar.Cutis.Fritz
open Set Function Filter LinearMap Matrix IsNilpotent
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Odom Lattice Nexus Loft
variable {G:Gauge}{E B R : Type*} [CommRing R][Algebra ℚ R]
variable [Fintype E][Fintype B](P:Lot E B R)(F:Fritz E B R) (r:R) (U:Floor E B R)
-- even or odd cohom roles
variable {p:Bool}
def δ (P:Lot E B R)(r:R): Module.End R (Floor E B R):= P.q r-touch (θ r) Finset.univ
lemma to_earth (h:FinRank U): FinRank (δ P r U):= ((Qh P r).leads h).sub h.touch
lemma dropping (h:Tone p U): Tone (!p) (δ P r U):=by cases p<;> exact ((Qb P r) _ U h).sub (touch_tone true _ _ _ _ h (Strip.work _))
variable [DecidableEq E][DecidableEq B] {q : ℕ}
private lemma ascend (h:Normal F P)(H:IsUnit r)(hp:FinRank U)(hv: Tone p U)(he:P.q r U=0)(hu: U []=0):
    ∃ S:Floor E B R, FinRank S ∧ Tone (!p) S ∧ U=P.q r S:=by
  let s:=(↑(H.unit⁻¹):R); have hr:r*s=1:=by nth_rw 1 [← H.unit_spec]; exact Units.mul_inv ..
  obtain ⟨n,hn⟩:=hp; let V (i) := rankn i U; let W (i) := dig R i • F.bud s (V i); refine ⟨∑ i∈ Finset.range (n+1), W i, ?_,Tone.sum _ _ (fun i _=> by cases p<;>exact ((bend F s) _ (V i) (rankn.tone _ U i hv)).smul _),?_⟩
  · refine FinRank.sum _ _ (fun i _=> ((clay_rises (F.bare s)).leads ⟨_, ((rankn.heg U i).cap _ _)⟩).smul _) -- fix
  rw [map_sum]; refine (Coil.ranks U n hn).symm.trans (Finset.sum_congr rfl (fun i _=>?_)); by_cases ht:i=0
  · subst i; have ht: V 0=0:=Coil.ext _ _ fun l=>by unfold V; rw [rankn_read]; cases l<;>simp [hu]
    change V 0=P.q r (_ • F.bud s (V 0)); rw [ht,map_zero,smul_zero,map_zero]
  unfold W; rw [map_smul]; have hl:=sups P F r s h hr (V i) ⟨_, (rankn.heg U i).cap _ _⟩; rw [show P.q r (V i)=0 from (Qh P r).takeout ⟨_,hn⟩ he, map_zero,zero_add, germ_eq (V i) i _ (fun l hl x hx=> Finset.mem_univ x) (rankn.heg U i)] at hl; rw [hl,dug (Nat.pos_of_ne_zero ht)]
lemma grounded (H:F.Fund P)(h:FinRank U)(he:δ P r U=0): P.q r (wither F.hop Finset.univ U)=0:= by rw [← show wither F.hop Finset.univ (δ P r U) = _ from F.chills P r H h, he]; exact wither_nil
lemma reverseH (H:F.Fund P) {S:Floor E B R}( _hg:FinRank U)(he:FinRank S)(hc: δ P r S=U): Fritz.eval F.hop U=0:= by rw [Fritz.eval,← hc, show wither _ _ (δ _ _ S)= _ from F.chills P r H he]; exact cold P r _
lemma weld (h:Normal F P)(H:IsUnit r)(hp:FinRank U)(hv:Tone p U)(he:δ P r U=0)(hy:Fritz.eval F.hop U=0):
    ∃ S:Floor E B R,FinRank S ∧ Tone (!p) S ∧ U=δ P r S:=by
  obtain ⟨Y,hj,hm,hk⟩:= ascend P F r _ h H hp.withering (felled hv F.hopGrade hp) (grounded P F r _ h.toFund hp he) hy
  refine ⟨wither (-F.hop) Finset.univ Y,hj.withering,felled hm (negativeGrade F.hopGrade) hj,?_⟩
  refine stoked (s:=Finset.univ) F.hopGrade (to_earth P r _ hj.withering) hp ?_; rw [show wither _ _ (δ _ _ _)= _ from F.chills P r h.toFund hj.withering]; rwa [backfit F.hopGrade hj]
-- free-resolution independence when other not known orthnormal. Useful tree gauge.
lemma anywhere (h:Normal F P)(T:Fritz E B R)(ht:T.Fund P)(H:IsUnit r)(hp:FinRank U)(hv: EvenT U)(he:δ P r U=0): eval T.hop U=eval F.hop U:=by
  let a:Floor E B R:=put ø (eval F.hop U); have hz:FinRank a:=FinRank.put _; let V:=U-a; have hg:FinRank V:=hp.sub hz; have hb : δ P r a=0:=by change cross true _ _ _ _- touch _ _ a=0; rw [touch_const, cross_put_right _ (Strip.work r),sub_self]
  have hh:eval F.hop V=0:=by dsimp only [eval,V,a]; rw [foe hp hz,wither_const]; exact sub_self _
  obtain ⟨S,hs,hS,hδ⟩ := weld P F r V h H hg (hv.sub (Tone.const _)) (by unfold V; rw [map_sub,hb,he,sub_self]) hh
  have ht:=reverseH P T r V ht hg hs hδ.symm; unfold eval V a at ht; rw [foe hp hz,wither_const,sub_read,sub_eq_zero] at ht; exact ht
end YM.MSBar.Cutis.Fritz
