import YM.SchemeConversionRG11.FirstW.Trice.Ember
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{c:ℕ→Side}{G:Gauge}{F:Labels.Frames G}{u:∀ i,Full.Grid (T.period i) 3}{p:Nodes} {W:Wash}{R:ℝ}{n:Side}
def tracC (x:Full.Grid n 3)(t:ℝ)(i j:P)(v:Players G 3 6):= ∑ a:Who G 6,∑ b:Who G 6,∑ c:Who G 6,changeD x t v (i,a) (j,b) (j,c)
lemma erased_tax (hp:p∈conf 3)(i j:P)(e:i≠j)(hx:i≠0)(a b c:Who G 6): amount p (dict (j,c) (dict (j,b) (dict (i,a) (SlateZ G))))=0:=by
 rcases tick_any hx with rfl|rfl
 · rcases full_order 0 j with rfl|he|he
   · rw [at1 (SlateZ G),at0 _,at0]; exact (erased_1 p hp a c b).1
   · exact False.elim (e (show 1=j from he.symm))
   rw [show j=2 from he,at1 (SlateZ G),at2 _,at2]; exact (erased_2 p hp a c b).1
 rcases full_order 0 j with rfl|he|he
 · rw [at2 (SlateZ G),at0 _,at0]; exact (erased_1 p hp a c b).2
 · rw [show j=1 from he,at2 (SlateZ G),at1 _,at1]
   exact (erased_2 p hp a c b).2
 exact False.elim (e (show 2=j from he.symm))
lemma wax_pair (d:Diorama T u p)(hg:G.Simple)(F:Labels.Frames G)(i j:P)(hx:i≠j)(h:i≠0)(A:Who G 6)(B:Who G 6)(C:Who G 6): Tendsto (fun k=> changeD (u k) (T.gap k) (SlateZ G) (i,A) (j,B) (j,C)) atTop (𝓝 0) := by
 let Q:=dict (j,C) (dict (j,B) (dict (i,A) (SlateZ G))); let X(k:ℕ):= echoLeg (T.gap k) (u k i) A.val (arise (T.gap k) (u k) (j,B)) (arise (T.gap k) (u k) (j,C))
 have HT : Tendsto (fun k=>ZeroR (u k) (T.gap k) Q) atTop (𝓝 0):=by have he:=fortune d Q; rw [show amount p Q=0 from erased_tax d.ht _ _ hx h ..] at he; exact he
 by_cases hv:A.val.fst≤2
 · obtain ⟨v,H⟩:= post_at (j,B) (j,C) i d (d.ht.ne hx.symm) (d.ht.ne hx.symm) _ hv; have hz:Tendsto X atTop (𝓝 v):= H; have ht:= (continuous_ofReal.continuousAt.tendsto.comp hz).mul HT; rw [mul_zero] at ht; apply ht.congr; intro k; dsimp only [X,Q,comp_def,changeD]
 have hp(k:ℕ) : ZeroR (u k) (T.gap k) Q=0:=by
    obtain ⟨L,H⟩:= pays_slot (dict (j,C) (dict (j,B) (SlateZ G))) i (u k) (T.gap k); have hm(t:Who G 6): (j,t)∈apart G 6 i:= Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx.symm⟩
    unfold Q; rw [show dict (i,A) (SlateZ G)=update (SlateZ G) i 0 from ?_,dict_b _ i (j,B) (hm B), dict_b _ i (j,C) (hm C),←H,map_zero]; rw [←basic_eq F]; exact congrArg (update _ i) (pder_end (basic F i) A (Nat.lt_of_not_ge hv) hg)
 apply tendsto_const_nhds.congr; intro k; unfold changeD; erw [hp]; rw [mul_zero]
end YM.RG11.FirstW.Branch
