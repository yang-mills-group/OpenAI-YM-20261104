import YM.RGComparison01.Marks.Stowe
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Stowe
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron
open Switch Mallow Ovens OmitClusters Song Refrain Motion
variable {η α: Type}
variable (M:ι→Lotus.Leaf R)(g:ι→ℝ)(H:Cash W s μ L Q o C T R) {b t k :ℕ} (Z:Cabinet η H b)
-- Flex for ANY dilation scores, even not full rooted
abbrev dilation (s:Finset ι)(f:ι→ℝ):=∏ i ∈ s,f i
def densityP (z: Cl M H):= ∏ i,dilation (z.2 i).2.val g
lemma drag (g':ι→ℝ)(z:Cl M H)(V:Config G c): Pillow.glass M (g*g') χ z V= densityP M g H z*glass M g' χ z V ∧ pottery M (g*g') χ z V=densityP M g H z*pottery M g' χ z V:=by
   have h i : Pillow.divAmt M (g*g') (S:=S) i=Pillow.divAmt M g i* Pillow.divAmt M g' i:= by unfold divAmt; simp [prod_mul_distrib]
   unfold densityP dilation glass pottery Gas.term; simp_rw [part,emberP,h, mul_assoc (_:ℝ), Finset.prod_mul_distrib]; unfold divAmt; constructor<;> ring
-- refined when all tally
lemma assort {β : Type} [DecidableEq α] [DecidableEq β] (H:Finset β)(p:β→Finset α) (hH : (H.biUnion p).card=∑i∈H,(p i).card)(q:α→ℝ) : ∏ i∈H, (∏ j∈p i,q j)=∏ i∈H.biUnion p,q i:= by
   induction H using Finset.induction_on with
   | empty=> simp
   | @insert i s hi ih=>
     rw [Finset.biUnion_insert, Finset.sum_insert hi] at hH; have he:= card_biUnion_le (s:=s) (t:=p); have hx:= card_union_add_card_inter (p i) (s.biUnion p); have ht : Disjoint (p i) (s.biUnion p):= Finset.disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
     rw [Finset.prod_insert hi,Finset.biUnion_insert,prod_union ht]; rw [Finset.card_union_of_disjoint ht] at hH; exact congr_arg (fun x => _ * x) (ih (Nat.add_left_cancel hH))
lemma defined (p:Finset ι)(z:Cl M H)(hp:Yielding M H p z): densityP M g H z=dilation p g:=by rw [←hp.1]; exact assort _ _ (Eq.symm (hp.2.trans (congr_arg Finset.card hp.1.symm))) g

variable (p:Finset ι)(z:Cl M H)
lemma travel (V:Finset ι)(x:ℝ): Ink.printer M H z x V= if recordSet M H z⊆ V then x^Season.allot z else 0:=by
   let f i:=(z.2 i).2.val; by_cases he: recordSet M H z⊆ V
   · unfold printer; rw [if_pos he]; change ∏ i,Switch.click (f i) 1 x V=x^(Season.allot z); have hv :∀ i, f i⊆ V:=fun i=> Finset.Subset.trans (subset_biUnion_of_mem f (mem_univ _)) he; simp_rw [click,if_pos (hv _),mul_one, Finset.prod_pow_eq_pow_sum, f]
   rw [if_neg he]; obtain ⟨i,h,hp⟩:= Finset.not_subset.mp he; obtain ⟨j,hj,ht⟩:=mem_biUnion.mp h; exact Finset.prod_eq_zero hj (show Switch.click (f j) 1 _ _=0 from if_neg (fun he=>hp (he ht)))
lemma code (hp:Yielding M H p z)(hq:p.Nonempty) (V:Config G c): Ink.yielded M g H (χ:=χ) z V= Switch.click p (pottery M g χ z V):= by
   funext x r; unfold yielded Ink.paths; rw [if_pos (show Season.allot z≠0 from hp.2.symm ▸ ((card_pos.mpr hq).ne')),travel, hp.1,hp.2]; unfold Switch.click; split; rfl; exact zero_mul _
lemma mode (V:Config G c) (h:¬Yielding M H p z): Switch.jet (Ink.paths M g H (χ:=χ) z V) p=0:= by
   let P' := recordSet M H z; let k:= Season.allot z-P'.card; let B:=pottery M g χ z V; let f x:= B*x^k; have ht : P'.card ≤ Season.allot z:= Finset.card_biUnion_le; let g' (x:ℝ):= Switch.bench P' (f x)
   have hf : Models (Ink.paths M g H (χ:=χ) z V) g':= by
      constructor
      · intro x hx; rw [show g' x=bench P' (f x) from rfl,(modelClick P' (f x)).current x hx]; funext p; unfold Ink.paths; rw [travel]; unfold click; by_cases he:P'⊆p
        · rw [if_pos he,if_pos (show recordSet M H z⊆ p from he)]; rw [← show P'.card+k=_ from Nat.add_sub_of_le ht,pow_add]; unfold f B; ring
        rw [if_neg he,if_neg (show ¬ recordSet M H z⊆p from he),zero_mul]
      intro r; unfold g' Switch.bench; split; next=> exact ((_root_.continuousAt_const.mul (continuousAt_id.pow k)).tendsto).mono_left nhdsWithin_le_nhds
      next=> exact tendsto_const_nhds
   rw [hf.exact]; by_cases hx:p=P'; swap; · exact if_neg hx
   have hz : k≠0:= by unfold k; intro hn; apply h; exact ⟨hx.symm,hx.symm ▸ (by omega : Season.allot z=P'.card)⟩
   unfold g' Switch.bench; rw [if_pos hx]; unfold f; rw [zero_pow hz,mul_zero]

lemma posted_jet (V:Config G c): Switch.jet (Ink.yielded M g H (χ:=χ) z V) p= if Yielding M H p z ∧ p.Nonempty then pottery M g χ z V else 0:= by
   let F : Ways ι:=yielded M g H (χ:=χ) z V; have hx (h:Season.allot z=0): jet F p=0:=by rw [show F= click ∅ 0 from funext fun x=>funext fun s=> (by simp [F,yielded,h,click]),(modelClick _ _).exact]; simp [bench]
   split
   next h=> rw [code M g H p z h.1 h.2,(modelClick _ _).exact]; exact if_pos rfl
   next h=> change Switch.jet F p=0; by_cases ht : Season.allot z=0; exact hx ht
            have hp: ¬Yielding M H p z:= fun hh=> h ⟨hh, Finset.card_pos.mp (show 0 < p.card from hh.2 ▸ Nat.pos_of_ne_zero ht)⟩
            rw [show F= _ from (show F= Ink.paths M g H (χ:=χ) z V from funext fun x=>funext fun p=> if_pos ht)]; exact mode M g H p z V hp
variable [Fintype ι]
lemma lowRibbon (T : Ribbon R n) (Ω : ℕ→ Prop) (hΩ:Drawing.Opens T Ω) (hl : ∀ i∈p,∀ j,(M i).turn=Wing.logKey j→ T.keep j) (V:Config G c)(hp : Yielding M H p z)(he:glass M g χ z V≠0)(h:¬ Season.Heavy k z)(hX : ¬ Season.Ode Ω z)(m:ℕ)(hm:p.card ≤ m): ∀ᶠ q in atTop,z ∈ ledger M H (Drawing.cabinet H T) (k+m) q p:=by -- requires fintype
   obtain ⟨hc,hv,hP⟩:= Canyon.minor V h hX he hΩ; let D:= Drawing.cabinet H T
   have hπ : struck M H p z:=⟨hp,fun i=> (hP i).2.2.2.1⟩
   have hz i : ((z.2 i).1.val : Set (Head S)) ⊆ Set.range D.ink:=by -- coercion need `(z.2 i).1.val.toSet`
     intro j hj; by_cases he' : j∈(z.2 i).2.reach
     · obtain ⟨k,hk,rfl⟩:=mem_image.mp he'; have hz':k∈p:= hp.1 ▸ mem_biUnion.mpr ⟨i,mem_univ i,hk⟩
       obtain ⟨l,hl'⟩:= (hP i).2.2.2.2.1 k hk; refine ⟨.inr ⟨l,hl k hz' l hl'⟩,?_⟩; unfold Palette.sign; rw [hl']; rfl
     exact (hP i).2.2.2.2.2 j (Finset.mem_sdiff.mpr ⟨hj,he'⟩)
   let f' i:= (z.2 i).1.val.preimage D.ink D.ink.injective.injOn
   have hZ i:D.shell (f' i)=(z.2 i).1.val := by
     ext j; constructor
     · intro h; obtain ⟨l,hl,rfl⟩:=mem_map.mp h; exact mem_preimage.mp hl
     intro h; obtain ⟨k,rfl⟩:= hz i h; exact mem_map_of_mem _ (show k∈f' i from mem_preimage.mpr h)
   have hA i:D.Peach (f' i):= by unfold Cabinet.Peach; rw [hZ]; exact (hP i).1
   have hK i:D.pile _ (hA i)= (z.2 i).1:= Subtype.ext (hZ i)
   let x : Cabinet.Parenthood _:= ⟨z.1,f'⟩
   have h1 : Season.allot z ≤ m:= hp.2 ▸ hm
   have hα : D.Scene (k+m) x:= by
     refine ⟨hc.trans (Nat.add_le_add_left h1 _),fun i=> ?_,hA,?_⟩
     · apply le_trans (b:=(z.2 i).1.val.card); · rw [← hZ]; exact (Finset.card_map ..).ge
       exact (hP i).2.2.1.trans (Nat.add_le_add_left h1 _)
     refine (show coefficient (blocked D.garden) x.2=coefficient (Baked.seam M H) z.2 from ?_).symm ▸ hv
     apply Meadow.movement; intro i j
     change f' i=f' j ∨ _ ↔ H.seam _ _
     unfold Cash.seam blocked; rw [←hK,← hK]; exact or_congr ⟨fun he=>Subtype.ext (congr_arg D.shell he),D.pines _ _ _ _⟩ Iff.rfl
   let W: D.Record (k+m):= ⟨x,hα⟩; filter_upwards [D.interns W] with i hi
   exact mem_filter.mpr ⟨(Stowe.posted ..).2 ⟨W,hi, show D.covers W= Canyon.pattern z from congr_arg (Sigma.mk z.fst) (funext hK)⟩,hπ⟩
end Stowe
end YM.RGComparison01.Pledge
