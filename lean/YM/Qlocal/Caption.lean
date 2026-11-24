import YM.Qlocal.Provisional
/-!
Travel of *all* field-independent external captions (on this branch even
multimarker ones, when transferred with one specified ancestor area). Preimages
here are the direct parent map; wider stencil remapping can pay from same
reserve currency using Footprint. Includes whole support; claim ONLY weighted
coefficient budget, not full readout integral. Densenormalization preserved.
 `Y.menu.global` assumed truly kept as captions, not hidden in Unit of Breath
(units zero if Peak). On changing geometry this leaves the sum ∑' all captions
 and reads untouched exactly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.StageArt
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Footprint
open Extra.Iteration
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{c f:Side}
    {P: RG.Rep G f}{P': RG.Rep G c}
    {X:Support f}{o:V→Site f}{s:V→Support f}
    {u w:V→ℝ}{z z':R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ ρ e:ℝ}
variable (S:StepData c f)
set_option quotPrecheck false
abbrev fly (p : Ratio c f) (L: Support f): Support c:= L.image p.parent
noncomputable abbrev cost (S:StepData c f)(α:ℝ):= (S.ratio.count.val:ℝ)^4 * Real.exp (α*Footprint.preCost 0)
-- direct transfer without requiring Anchored. λ+ unit memory unchanged
lemma transfer {m:ι→ℝ}{L:ι→Support f} {S:StepData c f}
   (hm:∀ i,0 ≤ m i)(h:Ac.Hit L k m a A)(he:k ≤ 2*k')(hk:0<k') (hb:0 ≤ b)
   (hv:b*Footprint.conversion (S.ratio) 0≤a) : Ac.Hit (fun i=>fly (S.ratio) (L i)) k' m b (cost S b * A):= by
 intro x; let y i:=(fly S.ratio (L i)); let W:=Real.exp (b*Footprint.preCost 0); have hp:=Footprint.footprint S.ratio 0 k' k; let r:= S.ratio.count.val
 have ht i: (m i)*Real.exp (b*coverNumber k' (y i)) ≤ W*(m i*Real.exp (a*coverNumber k (L i))):=by
    rw [mul_left_comm,← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hm _); have h(i):= Corona.cover_mono (show y i ⊆ enlargement S.ratio 0 k' (L i) from halo_subset _ _) k'
    refine (mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (h i)).trans (hp (L i) hk he)) hb).trans ?_; rw [mul_add, ← mul_assoc]; apply add_le_add_right; exact mul_le_mul_of_nonneg_right hv (by positivity)
 let F:= univ.filter fun i=> S.ratio.parent i=x; have hF: F.card ≤ r^4:= by simpa only [F,Finset.mem_singleton,Finset.card_singleton,one_mul] using (Footprint.crowd S.ratio {x})
 let f i p:= if p∈L i then W*(m i*Real.exp (a*coverNumber k (L i))) else 0
 have hx p: SumBudget (fun i=> f i p) (W*A):= by
    convert! budget_scale (show 0 ≤ W from Real.exp_nonneg _) (h p) using 1; ext i; unfold f; split; rfl;rw [mul_zero]
 refine budget_loosen (budget_mono (budget_over F (fun p i=> f i p) (fun _=>W*A) (fun p _=>hx p)) (fun i=>?_) (fun i=>?_)) ?_
 · split; exact mul_nonneg (hm _) (Real.exp_nonneg _); rfl
 · split; next hl=>
     obtain ⟨j,hj,hv⟩:= mem_image.mp hl; refine (ht i).trans (show _ from ((show f i j= W*(m i*Real.exp (a*coverNumber k (L i))) from if_pos hj) ▸ (show f i j≤_ from Finset.single_le_sum (?_) ?_))); -- fix synt
     · intro b _; exact (hx b).1 i
     exact mem_filter.mpr ⟨mem_univ _,hv⟩
   next=> exact sum_nonneg fun i _=> (hx i).1 _
 rw [sum_const,nsmul_eq_mul]; unfold cost; rw[mul_assoc]; have hR:F.card ≤ r^4:=hF; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hF) (mul_nonneg (Real.exp_nonneg _) (budget_nonneg (h 0))) -- ambiguity site

variable (Y:Taste Ω o P R) (Z:Taste Ω (S.ratio.parent ∘ o) P' R)
private abbrev bills:= numbering (ℕ⊕ℕ)
def stay : Taste Ω (S.ratio.parent ∘ o) P' R where
 menu:= Z.menu
 root:= Z.root
 tag := (Sum.elim Z.tag Y.tag ∘ bills)
 site := Sum.elim Z.site (fun i=>fly S.ratio (Y.site i)) ∘ bills
 score x := Sum.elim (Z.score x) (Y.score x) ∘ bills
variable {Z Y} {D D':Set (ℕ ×ℕ)}
local notation "Z✶"=> stay S Y Z
local notation "p★" => S.ratio.parent
lemma retained (h:RetainsDeclared D Y s) (hp: RetainsDeclared D' Z (fly S.ratio ∘ s)) : RetainsDeclared D' (stay S Y Z) (fly S.ratio ∘ s):= by
 refine ⟨hp.origins,hp.regular,hp.forced,hp.padding,fun i=>?_⟩
 simp only [stay, Function.comp_apply]; rcases bills i with i|i
 · exact hp.captions i
 exact fun x hx=> Finset.image_subset_image (h.captions i x hx) -- hx
lemma activate (x:Ω)(h:(Y.leaf x).Active)(hr:(Z.leaf x).Active): ((stay S Y Z).leaf x).Active:=by
 refine ⟨hr.articles,fun i=>?_,fun i=>?_⟩
 · simp only [stay, Taste.leaf, Function.comp_apply]; rcases bills i with i|i; exact hr.captions.card i; exact h.captions.card i
 simp only [stay, Taste.leaf, Function.comp_apply]; rcases bills i with i|i; exact hr.captions.pins i
 intro j hj; change Z.menu.origins j∈ _; rw [Z.root]; exact mem_image_of_mem _ (show o j∈_ from congr_fun Y.root j ▸ h.captions.pins i j hj)
variable {b'} (hp : Peak P o Y z a A B)(hQ: Peak P' (S.ratio.parent ∘ o) Z z' b d b')
    (ha:0≤a) (he:P.p.B ≤ 2* P'.p.B) (hk: b*Footprint.conversion S.ratio 0 ≤ a)(hb:0≤b)(hz:∀ i,0< z i)(hw:∀ i,0< z' i)
-- price ratio comparison nonquiet only. Enough for shared tag.
variable (h₁:0≤ρ)(hρ:∀ i,(i:R.Mode).val.Nonempty→ z' i ≤ ρ* z i)
include hp hQ h₁ hρ he hk hb hz hw
set_option maxHeartbeats 250000
omit hz in
lemma earned [Nonempty Ω] : Peak P' (S.ratio.parent ∘ o) (stay S Y Z) z' b (d+cost S b*(ρ*A)) b':= by
 obtain ⟨g,hg,hG,hZ⟩:= hp.captions; obtain ⟨v,hv,hV,hy⟩:= hQ.captions
 let y:= cost S b*(ρ*A); have hK: Ac.Hit (fun i=> fly S.ratio (Y.site i)) P'.p.B (fun i=> z' (Y.tag i)*g i) b y:=by
    have hv₀(i):0≤ z' (Y.tag i)*g i:= mul_nonneg (hw _|>.le) (hg i)
    apply transfer hv₀ _ he P'.p.B_pos hb hk
    intro i; refine budget_mono (budget_scale h₁ (hZ i)) (fun i=> ?_) (fun i'=> ?_); · split; exact mul_nonneg (hv₀ _) (Real.exp_nonneg _);rfl
    split; next hf=> dsimp only; rw [← mul_assoc, ← mul_assoc]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hρ _ ?_) (hg _)) (Real.exp_nonneg _); let x:Ω:= Classical.ofNonempty; exact (hp.active x).captions.card i'
    next=> rw [mul_zero]
 refine ⟨fun x=>activate S x (hp.active x) (hQ.active x),hQ.units, ?_,?_,hQ.forced⟩
 · obtain ⟨c',hr,hl,hT⟩:= hQ.regular; exact ⟨c',hr,hl,fun i=> budget_loosen (hT i) (le_add_of_nonneg_right (budget_nonneg (hK 0)))⟩
 let V(i:ℕ⊕ℕ):= Sum.elim v g i; refine ⟨V ∘ bills,fun i=> ?_,fun x i=>?_,fun i=>?_⟩
 · unfold Function.comp V; rcases bills i with j|j; exact hv j; exact hg j
 · simp only [stay,V,Function.comp_apply]; rcases bills i with j|j; exact hV x j; exact hG x j
 let p(i:ℕ⊕ℕ):=Sum.elim Z.site (fly S.ratio ∘ Y.site) i; let r:=Sum.elim Z.tag Y.tag; let g j:=if i∈p j then z' (r j)*V j*Real.exp (b*coverNumber P'.p.B (p j)) else 0
 have hv: SumBudget g (d+y):= Extra.Iteration.Cost.sum (f:=g) (hy i) (hK i)
 exact budget_pull bills bills.injective hv
-- note exact equality, not using proximity of evaluations etc.
omit h₁ hρ he hk hp hQ hz hw hb
section famed
variable {L:Taste Ω o P R} (H:Peak P o L z a A B) (x:Ω) (hωh:∀ i,0<z i)
include ha H hωh x
lemma colourCost : ∃ f:ℕ→ℝ,Summable f∧(∀ i,0≤ f i)∧∀ y i, ‖L.score y i‖≤f i:= by
 obtain ⟨f,hf,hF,hT⟩:= H.captions; refine ⟨f,receives hf hωh (p:=P.p) ha (fun i=>?_) hT,hf,hF⟩; obtain ⟨z,hz⟩:= (H.active (x)).captions.card i; exact ⟨_,(H.active (x)).captions.pins i z hz⟩ -- include x?
lemma poised : Summable (fun i=> Poly.send (L.tag i) (L.score x i)):= by obtain ⟨f,hf,-,h⟩:= colourCost ha H x hωh; exact (ghost (hf.of_norm_bounded (fun i=>h x i))).2
lemma mute : ((L.leaf x).captions.chord).part R.quiet=0:= by
 unfold Captions.chord; rw [Poly.share]; apply (tsum_congr ?_).trans tsum_zero; intro i; rw [Poly.part_send, if_neg ?_]; intro he; exact (H.active x).captions.card i|>.ne_empty (congr_arg Subtype.val he.symm); exact poised ha H x hωh
include x -- supports Ω
lemma light_funds_ : ∃ f : ℕ→ℝ, Summable f∧ (∀ y i U, ‖clipped L y i U‖≤ f i):=by
 obtain ⟨f,hf,hF,hT⟩:=H.regular; let t:= H.active x; have hv i:(L.menu.branch i).Nonempty:= by obtain ⟨p,hp⟩:=t.articles.proper i; exact ⟨_,t.articles.pins i p hp⟩
 refine ⟨f, receives hf hωh (p:=P.p) ha hv hT, fun y i U=>?_⟩; by_cases hp:Healthy P.p.threshold (L.menu.branch i) U
 · unfold clipped; rw [masked_eq _ _ _ _ hp]; exact (hF _ _ (hv i).choose (hv i).choose_spec).2 _ hp [] (Nat.zero_le _) (by simp)
 unfold clipped; rw [masked_ne _ _ _ _ hp,norm_zero]; exact hf _
variable [Fintype V]
lemma nozoom (V:Config G f) : ((L.leaf x).contents.extra V).part R.quiet=0:=by
 obtain ⟨f,hf,h⟩:=light_funds_ ha H x hωh; let t i:= clipped L x i V; let v i := Poly.send (L.menu.rays i) (t i); have hv:Summable v:= (ghost (hf.of_norm_bounded (fun i=> h x i V))).2
 change ((∑ i,Poly.send _ (L.menu.global x i))+ (∑' i,v i)).part R.quiet=0
 rw [Poly.part_plus,Poly.part_sum,Poly.share hv]
 have ht i:(v i).part R.quiet=0:= by refine (Poly.part_send ..).trans (if_neg ?_); intro hy; exact ((H.active x).articles.proper i).ne_empty (congr_arg Subtype.val hy.symm)
 simp only [ht,H.units,Poly.send_zero,Poly.part_nil,sum_const_zero, tsum_zero, zero_add]
lemma detached (V:Config G f) : (L.leaf x).density V= Poly.pass ((L.leaf x).captions.chord) * (L.leaf x).contents.density V:= by
 unfold RG3.Forms.Deck.density RG3.Forms.Deck.log Overlay.Bands.density; rw [add_comm ((L.leaf x).contents.extra V), Extra.Trajectories.pass_add (mute ha H x hωh) (nozoom ha H x hωh V), mul_smul_comm, mul_assoc]



end famed
include hp hQ hz hw hb ha
lemma stored (x:Ω): ((stay S Y Z).leaf x).captions.chord= (Z.leaf x).captions.chord+(Y.leaf x).captions.chord:= by
 let f(i:ℕ⊕ℕ):= Sum.elim (fun i=> Poly.send (Z.tag i) (Z.score x i)) (fun i=> Poly.send (Y.tag i) (Y.score x i)) i
 unfold Captions.chord; rw [tsum_congr (g:=f ∘ bills) ?_];
 · exact (bills.tsum_eq f).trans (Summable.tsum_sum (f:=f) (poised hb hQ x hw) (poised ha hp x hz)) -- argument order
 intro i; simp only [Taste.leaf, stay,comp_apply]; unfold f; rcases bills i with j|j <;> rfl

variable [Fintype V]
lemma incumbent (x:Ω)(Vw:Config G c): ((stay S Y Z).leaf x).density Vw= Poly.pass ((Y.leaf x).captions.chord) * (Z.leaf x).density Vw:= by
 unfold RG3.Forms.Deck.density RG3.Forms.Deck.log; let a:= (Y.leaf x).captions; let b:= Z.leaf x; let U:= Vw
 rw [stored S hp hQ ha hb hz hw];
 change ((Real.exp (P'.exponent Vw):ℝ):ℂ) • ((Poly.pass ((b).contents.extra Vw+((b).captions.chord+(a).chord)))* (b.contents.cluster Vw))= _; have hp' : a.chord.part R.quiet=0:= mute ha hp x hz; have hv' : _root_.YM.Marker.Poly.part (b.contents.extra Vw+b.captions.chord) R.quiet=0:= (Poly.part_plus ..).trans (by rw [show (b.contents.extra _).part _=_ from (?_: (b.contents.extra Vw).part R.quiet=0), show b.captions.chord.part _=_ from (mute hb hQ x hw: b.captions.chord.part R.quiet=0), zero_add]; exact nozoom hb hQ x hw Vw)
 rw [← add_assoc, add_comm _ (a).chord, Extra.Trajectories.pass_add hp' hv', mul_assoc, mul_smul_comm]
end YM.Qlocal.StageArt
