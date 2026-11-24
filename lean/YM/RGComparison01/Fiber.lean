import YM.RGComparison01.Speaker

/-!
# Cut bouquet and paid alternative tail

 Any choice of Ribbon covering the remaining short nonzero E. The
 actual hard reservation remains; masks of originals retained and not
 shifted here. Covers EVERY remaining nonzero kernel on any V (zero
 on all fields includes fringe masks). -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {ℓ M n k b : ℕ} {ι χ : Type} {K : Teller G} {P : Patch}
variable {s W a U u : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
    {κ: Chi} {c f C F L₀: Side} {S:StepData c f} {T : Tube G S} {R : RG.Rep G f}
    {I : Cash W s a L₀ X o U T R}
section frame
namespace Drawing
variable (B : Ribbon R n) (Ω : ℕ→Prop)
/-- Partition guard: rough inputs with Ω; all other *possibly* seen E
 jobs covered across all fields. -/
structure Opens : Prop where
  except i : Ω i → ¬ B.keep i
  anywhere i : ¬ Ω i → ¬ B.keep i → ∀ V,R.activities.regularOccurrence R.p i V=0
lemma spins (η : Chi) (V : Config G c) (p : I.ThinP) (i : ℕ) (hp : Opacity.key S i∈p.val)
    (he : ∀ V,R.activities.regularOccurrence R.p i V=0) : March.leaflet I η V p=0 := by
  unfold March.leaflet Pond.likely Stained.fringe
  have hx (F:Tree.Forest S.ratio) (Y:Coat T F) J z : Polar.floating Y o.a R W X.table z J X.halo p.val=0 := by
    apply prod_eq_zero hp; change Real.exp (-(R.activities.regularOccurrence _ i _) * _) -1= _; rw [he,neg_zero,zero_mul,Real.exp_zero,sub_self]
  have hv (F:Tree.Forest S.ratio) (Y:Coat T F): Shield.shelter Y W o.a p.val R X.table X.halo=0 := by
    unfold Shield.shelter; split; next _=> unfold Shield.seating; simp only [Shield.bars,Pond.likely,hx,mul_zero,integral_zero,sum_const_zero]
    rfl
  simp only [hv,integral_zero,sum_const_zero,mul_zero]
open Selector Cabinet
lemma depth_music {z : I.fragrances} (ht : Height.depth I z<radiusB s) (p : Music c f) (i) (hv : disc S p∈ (z.2 i).val) :
    verse R.path p ≤ radiusB s:= by
  apply (Nat.cast_le (α:=ℝ)).mp
  apply le_trans (b:=I.shapeW (z.2 i).val) ?_ ((single_le_sum (f:=fun i=>I.shapeW (z.2 i).val) (fun j _=>I.positive_volume _) (mem_univ i)).trans ht.le)
  apply le_trans ?_ (single_le_sum (s:=(z.2 i).val) _ hv)
  swap
  · intro i hi; apply add_nonneg (Nat.cast_nonneg _) (show 0 ≤ Mixed.lengths S I.faresP (ConnectedActivityE6.lengths T R) i from (by
      rcases i with i|i
      · exact mul_nonneg I.laws.acquired.extra (Nat.cast_nonneg _)
      exact I.armed.extra _))
  rw [Mint.balance T R p]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)

lemma permute (h : Opens B Ω) (η : Chi) (V : Config G c) (p : I.fragrances) (hp : ¬ Selector.Weeds ℓ p)
    (he : ¬ Selector.Inherited Ω p) (ht : stream I η V p ≠ 0) : p∈ Set.range (Cabinet.bureau (Drawing.cabinet I B) ℓ) := by
  let C:=Drawing.cabinet I B
  obtain ⟨h₀,h₁,h₂,-,hP⟩:= Selector.left_low Ω hp he V ht
  have hv i : coefficient I.seam p.2≠0∧leaflet I η V (p.2 i)≠0 :=
    ⟨fun he=>ht (by unfold stream Gas.term; rw [he,zero_mul,zero_div]),fun he=>ht (by unfold stream Gas.term; rw [prod_eq_zero (mem_univ i) he,mul_zero,zero_div])⟩
  have hx i k (hi:k∈ (p.2 i).val) : k∈Set.range C.ink:= by
    rcases (hP i).2 k hi with ⟨j,hj,rfl⟩|H
    · have hh : B.keep j := by by_contra h'; exact (hv i).2 (spins η V _ j hi (h.anywhere j hj h'))
      exact ⟨.inr ⟨j,hh⟩,rfl⟩
    obtain ⟨x,hx⟩:= (Mint.penned ..).1 H
    exact ⟨.inl ⟨x,depth_music h₂ x i (hx.symm ▸ hi)⟩, (show C.ink _ = _ from hx)⟩
  let f i:= (p.2 i).val.preimage C.ink C.ink.injective.injOn
  have hZ i:C.shell (f i)=(p.2 i).val := by
    ext j; constructor
    · intro h; obtain ⟨l,hl,rfl⟩:=mem_map.mp h; exact mem_preimage.mp hl
    intro h; obtain ⟨k,rfl⟩:= hx i j h; exact mem_map_of_mem _ (show k∈f i from mem_preimage.mpr h)
  have hA i:C.Peach (f i):= by unfold Peach; rw [hZ]; exact (hP i).1
  have hK i : C.pile _ (hA i)=p.2 i := Subtype.ext (hZ i)
  let x : Parenthood (Count B I):= ⟨p.1,f⟩
  have hT : Scene C ℓ x:= by
    refine ⟨h₀.le,fun i=> ?_,hA,?_⟩
    · apply le_trans (b:=(p.2 i).val.card); · rw [← hZ]; exact (Finset.card_map ..).ge
      exact (single_le_sum (f:=fun i=> (p.2 i).val.card) (fun j _=> Nat.zero_le _) (mem_univ _)).trans h₁.le
    refine (show coefficient (blocked C.garden) x.2=coefficient I.seam p.2 from ?_).symm ▸ (hv none).1
    apply Meadow.movement; intro i j; rw [← hK,← hK]; exact or_congr ⟨fun he=>Subtype.ext (congr_arg C.shell he),C.pines _ _ _ _⟩ Iff.rfl
  refine ⟨⟨x,hT⟩,?_⟩; change Sigma.mk p.fst _=p; congr 1; exact funext hK
lemma vacant (h : Opens B Ω) (p : Cabinet.Record (Drawing.cabinet I B) ℓ) : ¬ Selector.Inherited Ω ((Drawing.cabinet I B).bureau ℓ p):= by
  let C:=Drawing.cabinet I B
  rintro ⟨i,hi,j,h⟩; obtain ⟨k,hk,hK⟩:=mem_map.mp (show Opacity.key S i∈ C.shell _ from h); rcases k with k|k
  · have hx : Mint.note k.val=.inl (.inl i) := Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hK))
    exact payer _ _ hx
  have he : (k.val:ℕ) = i:= by
    exact Sum.inl_injective (Sum.inl_injective (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hK))))
  exact ‹Opens B Ω›.except _ hi (he ▸ k.property)
end Drawing
end frame
namespace Cabinet
variable (D : Cabinet ι I b)

-- stage posting exact
def catalogue (ℓ k : ℕ) : Finset (Magazine I) := disjSum ((D.podium ℓ k).map (D.bureau ℓ)) ((univ ×ˢ Meadow.ripened T.down (radiusB s) k).map (Meadow.rollers c).toEmbedding)
def board (ℓ k : ℕ) : Finset ℕ := (univ ×ˢ D.catalogue ℓ k).map (pennant I).symm.toEmbedding
lemma earns (i:ℕ) : i∈D.board ℓ k↔ (pennant I i).2∈D.catalogue ℓ k:= by unfold board; simp only [mem_map_equiv,mem_product]; simp
lemma tides (p : I.fragrances) (h : p∈Set.range (D.bureau ℓ)) : ∀ᶠ k in atTop,.inl p∈D.catalogue ℓ k := by
  obtain ⟨v,rfl⟩:=h; filter_upwards [D.interns v] with k hk; exact inl_mem_disjSum.mpr (mem_map_of_mem _ hk)
lemma rains (ℓ : ℕ) (p : Songbook c) (h : Meadow.arc T.down p≤radiusB s) : ∀ᶠ k in atTop,.inr p∈ D.catalogue ℓ k := by
  obtain ⟨⟨r,t⟩,hv⟩:= (Meadow.rollers c).surjective p
  have he : Meadow.melody T.down t≤radiusB s:= by rw [← Meadow.arc_receipt T.down r t,show Meadow.legs r t=p from hv]; exact h
  filter_upwards [Meadow.burgeoning T.down _ t he] with k hk; exact inr_mem_disjSum.mpr (mem_map.mpr ⟨(r,t),mem_product.mpr ⟨mem_univ _,hk⟩,hv⟩)
end Cabinet
end YM.RGComparison01
