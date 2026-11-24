import YM.Qlocal.Reckoner.Paper
/-!
# Exact mask read editions and annotated payments.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison
variable {V Ω J J' J₀:Type}[DecidableEq V]{G:Gauge}{n:Side}{R:Census V}
variable {X: RG.Rep G n}{s:V→ Support n}{q:Ray R} {A B t t':ℝ}
namespace Scribe
open Next.Foundations
variable (S:Scribe Ω J G n R) (T:Scribe Ω J' G n R) (p:BudgetPoint) (F:J→Prop) (K:Ω→Policy G R n)
noncomputable def pile : Scribe Ω (J⊕J') G n R := ⟨Sum.elim S.tag T.tag, Sum.elim S.region T.region, Sum.elim S.total T.total, fun x=>Sum.elim (S.score x) (T.score x)⟩
noncomputable def view (f:J'→J) : Scribe Ω J' G n R:= ⟨S.tag ∘ f,S.region ∘ f,S.total ∘ f,fun x=>S.score x∘ f⟩
noncomputable def eligible : Scribe Ω J G n R:= {S with score:=fun x i=> if F i then S.score x i else 0}
noncomputable def shade (f:Ω→J→ℂ) : Scribe Ω J G n R:= {S with score:= fun x i=> (f x i) • S.score x i}
noncomputable abbrev discount : Scribe Ω J G n R:= S.shade fun _ _=> -1
variable {p S T}
variable (ha:S.Proper p s) (hb:T.Proper p s) (hu:S.Spend p q t A) (hk:T.Spend p q t B) (hc: Rental q)
include ha
lemma Proper.pile (hb:T.Proper p s): Proper (S.pile T) p s:= by
 refine ⟨?_,?_,?_,?_,?_⟩
 · rintro (i|i); exact ha.length _; exact hb.length _
 · rintro i (j|j); exact ha.sight ..; exact hb.sight ..
 · rintro (i|i) v x U; exact ha.owns i v x U; exact hb.owns i v x U
 · rintro (i|i); exact ha.quiet _; exact hb.quiet _
 rintro (i|i); exact ha.total _; exact hb.total _
omit ha
include hu hk
lemma Spend.pile : Spend (S.pile T) p q t (A+B):=by
 obtain ⟨u,hu,ht⟩:=hu; obtain ⟨v,hv,hV⟩:=hk; let P:= S.pile T; let g:=Sum.elim u v; refine ⟨g,⟨?_,?_⟩, fun x=> Extra.Iteration.Cost.sum ?_ ?_⟩
 · rintro (i|i); exact hu.nonneg _; exact hv.nonneg _
 · rintro x (i|i); exact hu.bound x i; exact hv.bound x i
 · exact ht x
 exact hV x
include ha hb hc hu hk
set_option maxHeartbeats 300000
lemma pool (h:0 ≤ t)(x y): (S.pile T).send p x y=S.send p x y+T.send p x y:= Summable.tsum_sum (f:=(S.pile T).enters p x y) (Scribe.cost_read hu hc ha h x y) (Scribe.cost_read hk hc hb h x y)
omit ha hb hc hu hk
include ha
lemma Proper.eligible : Proper (S.eligible F) p s:= by
 constructor
 · exact ha.length
 · intro i j; unfold Scribe.eligible; dsimp only; split; exact ha.sight ..; exact (Extra.Histories.regular0 _ _ 0).1 -- need anchor
 · intro i v x U; unfold Scribe.eligible; dsimp only; split; exact ha.owns i v x U; intro he; exact (he rfl).elim
 · intro i he x; unfold Scribe.eligible; dsimp only; split; exact ha.quiet _ he _; rfl
 intro i x y hy; unfold Scribe.eligible; dsimp only; split; exact ha.total i x y hy; rfl -- `..`
lemma Proper.shade (f:Ω→J→ℂ): Proper (S.shade f) p s:= by
 constructor
 · exact ha.length
 · exact fun x i=> regular_smul _ (ha.sight x i)
 · exact fun i v x U hx=> ha.owns i v x U (right_ne_zero_of_mul hx)
 · intro i he x; unfold Scribe.shade; dsimp only; rw [ha.quiet i he,smul_zero]
 exact fun i x y ht=> congr_arg ((f x i)*·) (ha.total i x y ht)
omit ha
include hu
lemma Spend.loosen (h:A ≤ B) : Spend S p q t B:= by obtain ⟨f,hf,he⟩:=hu; exact ⟨f,hf, fun i=> budget_loosen (he i) h⟩
lemma Spend.nonneg : 0 ≤ A:= by obtain ⟨f,hf,h⟩:=hu; exact budget_nonneg (h 0)
include hc
lemma Spend.narrow (h:t' ≤ t): Spend S p q t' A:=by
 obtain ⟨f,hf,hS⟩:=hu; refine ⟨f,hf,fun x=> budget_mono (hS x) (fun i=> ?_) (fun i=> ?_)⟩
 · split; exact mul_nonneg (mul_nonneg (hc.pos _|>.le) (hf.nonneg _)) (Real.exp_nonneg _);exact le_rfl
 split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right h (by positivity))) (mul_nonneg (hc.pos _|>.le) (hf.nonneg _)); exact le_rfl
omit hc
lemma Spend.eligible : Spend (S.eligible F) p q t A:=by
 obtain ⟨f,hf,h⟩:=hu; refine ⟨f,⟨hf.nonneg,fun i j x hx=>?_⟩,h⟩; unfold Scribe.eligible; dsimp only; split; exact hf.bound i j _ hx; exact Push.Local.bound_weaken (Extra.Histories.regular0 ..).2 (hf.nonneg _)
lemma Spend.shade (W:Ω→J→ℂ)(h:∀ x i, ‖W x i‖≤B)(hb:0 ≤B): Spend (S.shade W) p q t (B*A):= by
 obtain ⟨f,hf,h⟩:= hu; let g i:= B*f i; refine ⟨g, ⟨fun i=> mul_nonneg hb (hf.nonneg i), fun x i j hj=> Push.Local.bound_weaken (bound_smul (W x i) (hf.bound x i j hj)) (mul_le_mul_of_nonneg_right (by apply_assumption) (hf.nonneg i))⟩,fun x=>?_⟩
 convert! budget_scale hb (h x) using 1; ext i; simp only [Scribe.shade,g]; split_ifs <;> ring
lemma Spend.discount : Spend S.discount p q t A:= by convert! Spend.shade hu (fun _ _=> (-1:ℂ)) (B:=1) (fun _ _=>by norm_num) zero_le_one; ring
omit hu
include ha
lemma Proper.view (f:J'→J): Proper (S.view f) p s:=⟨fun i=>ha.length _, fun x i=> ha.sight ..,fun i=>ha.owns _,fun i=>ha.quiet _,fun i=>ha.total _⟩
omit ha
include hu
lemma Spend.view (f:J'→J)(hf: Injective f): Spend (S.view f) p q t A:= by
 obtain ⟨g,hg,h⟩:=hu; exact ⟨g∘ f, ⟨fun i=>hg.nonneg _,fun i j=>hg.bound i (f j)⟩, fun i=> budget_pull f hf (h i)⟩
omit hu
lemma render_off (x i U): (S.eligible F).render p x i U=if F i then S.render p x i U else 0:=by
 unfold render eligible
 dsimp only; by_cases h:F i <;> by_cases hx:S.total i <;> simp only [h,hx,↓reduceIte, masked,Pi.zero_apply] <;> simp
lemma enters_off (x i U): (S.eligible F).enters p x U i=if F i then S.enters p x U i else 0:=by unfold enters; rw [render_off]; split; rfl; exact Poly.send_zero _
lemma render_shade (S:Scribe Ω J G n R) (f:Ω→J→ℂ) (p:BudgetPoint)(x i U): (S.shade f).render p x i U= f x i • S.render p x i U:= by
  unfold Scribe.shade render; dsimp only; split; rfl
  by_cases hz: Healthy p.threshold (S.region i) U; rw [masked_eq _ _ _ _ hz, masked_eq _ _ _ _ hz]; rfl; rw [masked_ne _ _ _ _ hz, masked_ne _ _ _ _ hz, smul_zero]
lemma enters_shade (S:Scribe Ω J G n R) (f:Ω→J→ℂ) (p:BudgetPoint) (x i U): (S.shade f).enters p x U i=f x i • S.enters p x U i:= by unfold enters; rw [render_shade]; exact (MergeProof.Menu.sent ..).symm -- check `Menu.sent`
lemma send_discount (S:Scribe Ω J G n R)(p:BudgetPoint)(x y): S.discount.send p x y= -S.send p x y:= by unfold send discount; simp_rw [enters_shade, neg_smul,one_smul]; exact tsum_neg ..
include ha hu hc
lemma split_Book (h:0 ≤ t)(x y): S.send p x y= (S.eligible F).send p x y+(S.eligible fun j=>¬F j).send p x y:=by
 unfold send; rw [← Summable.tsum_add (Scribe.cost_read (hu.eligible F) hc (ha.eligible F) h x y) (Scribe.cost_read (hu.eligible fun j=>¬F j) hc (ha.eligible fun j=>¬F j) h x y)]; exact tsum_congr fun i=>by_cases (p:=F i) (fun ht=>by simp only [enters_off,ht,↓reduceIte,not_true,add_zero]) (fun ht=>by simp only [enters_off,ht,↓reduceIte,not_false_eq_true,zero_add])
omit ha hu hc
lemma eligible_repeats (L:J→Prop) (S:Scribe Ω J G n R) : (S.eligible L).eligible F=S.eligible fun i=>F i∧L i := by
  unfold eligible; congr 1; funext x i; by_cases h: L i <;> by_cases H:F i <;> simp [h,H]
-- assembly witnesses: if can pay the two classify.
variable {u v:ℝ} (hx:(S.eligible F).Spend p q t u) (hs:(S.eligible fun i=>¬ F i).Spend p q t v)
include hx hs
lemma Spend.joint : Spend S p q t (u+v):=by
 obtain ⟨f,hf,hF⟩:=hx; obtain ⟨g,hg,hG⟩:=hs; refine ⟨f+g, ⟨fun i=> add_nonneg (hf.nonneg _) (hg.nonneg _), fun x i u he=>?_⟩, fun i=>?_⟩
 · rcases Classical.em (F i) with h|h; · refine Push.Local.bound_weaken ?_ (le_add_of_nonneg_right (hg.nonneg _)); convert! hf.bound x i u he using 1; simp only [Scribe.eligible,h,true_and,not_false_eq_true,if_true] -- risk struct
   refine Push.Local.bound_weaken ?_ (le_add_of_nonneg_left (hf.nonneg _)); convert! hg.bound x i u he using 1; simp only [Scribe.eligible,h,true_and,not_false_eq_true,if_true]
 let U:= S.eligible F; convert! budget_plus (hF i) (hG i) using 1; ext j; simp only [Scribe.eligible, Pi.add_apply]; split_ifs <;> ring
end Scribe
end YM.Qlocal.Reckoner
