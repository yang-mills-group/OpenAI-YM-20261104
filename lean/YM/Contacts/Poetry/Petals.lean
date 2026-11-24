import YM.Contacts.Poetry.Yard
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Duet
/-! adapting Meadow/{Oriole,Reframe,Blox,Duet}. Anchor support of Pterography. Keeps actual signs. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Poetry
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j n₀ m₀ m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
open Meadow (spin garnerAt garner share portions regularA nonnegative paysOne honor melody ripened burgeoning arc_receipt arc bough spurs  Rags legs rollers)
variable {Ξ:Lecturer R' m₀}{Ξ₀:Lecturer R m₀}
def keep (I : Cash W p a L₀ X o U T R') (Ξ: Lecturer R' m₀) (n:ℕ) (i: Magazine I): Prop:= i.elim (fun i=>i∉Set.range (booths I Ξ n)) (fun i=> B< arc T.down i)
def bouquet (I:Cash W p a L₀ X o U T R')(Ξ:Lecturer R' m₀)(n₀:ℕ) (k:ℕ): Finset (Magazine I):= disjSum ((Poetry.calendar I Ξ n₀ k).map (booths I Ξ n₀)) ((univ ×ˢ (ripened T.down B k)).map (rollers c).toEmbedding)
lemma notKept (z:Magazine I) (h:z ∈ bouquet I Ξ n₀ m) : ¬Poetry.keep I Ξ n₀ z:= by
  unfold bouquet at h; rcases z with z|z
  · obtain ⟨i,hi,hz⟩:= mem_map.mp (inl_mem_disjSum.mp h); exact fun he=> he ⟨i,hz⟩
  obtain ⟨⟨s,i⟩,hi,hz⟩:= mem_map.mp (inr_mem_disjSum.mp h); have ht : arc T.down z≤ B:= by rw [← (show legs s i=z from hz),arc_receipt]; exact (mem_filter.mp (mem_product.mp hi).2).2
  exact fun h=> not_lt.mpr ht h
lemma unfurls (z:Magazine I) (hp:¬Poetry.keep I Ξ n₀ z): ∀ᶠ m in atTop,z∈bouquet I Ξ n₀ m:= by
  rcases z with z|z
  · change ¬z∉_ at hp; obtain ⟨w,rfl⟩: z ∈ Set.range (booths I Ξ n₀):= Classical.byContradiction hp; filter_upwards [retires w] with m hm; exact inl_mem_disjSum.mpr (mem_map_of_mem _ hm)
  obtain ⟨⟨s,i⟩,hv⟩:= (rollers c).surjective z
  have h: Meadow.melody T.down i≤ B:= by rw [← arc_receipt T.down s i, show legs s i=z from hv]; exact le_of_not_gt hp
  filter_upwards [burgeoning T.down B i h] with m hm; exact inr_mem_disjSum.mpr (mem_map.mpr ⟨(s,i),mem_product.mpr ⟨mem_univ _,hm⟩,hv⟩)

def debris (I:Cash W p a L₀ X o U T R')(Ξ:Lecturer R' m₀)(n₀:ℕ) (k:ℕ) (w:ℕ) := ¬Poetry.keep I Ξ n₀ (Song.pennant I w).2∧ (Song.pennant I w).2∉ bouquet I Ξ n₀ k
lemma dissolved (I:Cash W p a L₀ X o U T R')(Ξ:Lecturer R' m₀)(n₀:ℕ) (w:ℕ): ∀ᶠ k in atTop,¬debris I Ξ n₀ k w := by
  by_cases h:Poetry.keep I Ξ n₀ (Song.pennant I w).2
  · filter_upwards with k using (fun hx=> hx.1 h)
  exact (unfurls _ h).mono fun k h H=> H.2 h


section petals
variable (I Ξ n₀) (k:ℕ)
def panel : Finset ℕ := (univ ×ˢ (Poetry.bouquet I Ξ n₀ k)).map (pennant I).symm.toEmbedding
variable {k}
lemma petaled (i:ℕ) : i∈panel n₀ I Ξ k ↔ (pennant I i).2∈Poetry.bouquet I Ξ n₀ k:= by
  unfold panel; simp only [mem_map_equiv,mem_product]; simp

end petals
section apo
variable (I Ξ n₀) (p' : BudgetPoint) (x:Site c)
-- radius ℓ; purch post c
abbrev studio (l b m₀ n₀:ℕ) := roomP l b m₀ n₀ + 2*b
local notation "D''" => Poetry.studio X.halo B m₀ n₀
lemma modest (i: Magazine I) (hv: i∈Poetry.bouquet I Ξ n₀ m) (hB:p'.B=B) (ht: share I p' x i≠0): x∈(Beam.contents I p' i).support ∧ (Beam.contents I p' i).support⊆ neighbors D'' x := by
  rcases i with i|i
  · obtain ⟨⟨z,hz⟩,hi,rfl⟩:= mem_map.mp (inl_mem_disjSum.mp hv)
    let z':=vintage z hz; have he: x∈perf I z':= by contrapose! ht; exact if_neg ht
    change x∈(Beam.dashboard I z').support ∧ (Beam.dashboard I z').support ⊆_; rw [Beam.see]
    exact ⟨he, fun i hi=>(neighbors_mem ..).mpr (((neighbors_mem ..).1 (entered hz x he hi)).trans (Nat.le_add_right ..))⟩
  obtain ⟨⟨s,i'⟩,he,rfl⟩:=mem_map.mp (inr_mem_disjSum.mp hv); have hf : Meadow.melody T.down i'≤ B:= (mem_filter.mp ((mem_product.mp he).2)).2
  let k:= strings T.down p' (legs s i'); have he:k.site=x:= by contrapose! ht; exact if_neg ht
  change x∈k.support∧ k.support⊆_
  refine ⟨he ▸ k.anchor,?_⟩; rw [show x=s.2 from he.symm.trans (Meadow.tunesAnchor ..)]; intro x hx; have h:= (neighbors_mem ..).1 (Meadow.yarn T.down p' s i' hx); apply (neighbors_mem ..).2; dsimp only [Poetry.studio]; omega
lemma assigned (i:ℕ) (h : i∈Poetry.panel n₀ I Ξ m) (hB:p'.B=B) (hp:garnerAt I p' x i≠0):x∈((Beam.marquee I p').reg i).support ∧ ((Beam.marquee I p').reg i).support⊆ neighbors D'' x:= by
  let p:=Song.pennant I i; let θ:=spin p.1; let u:=θ.symm x
  obtain ⟨hy,hz⟩:=modest n₀ I Ξ p' u p.2 ((petaled n₀ I Ξ i).1 h) hB hp
  change x∈ Finset.image θ _ ∧ Finset.image θ (Beam.contents I p' p.2).support⊆ _
  refine ⟨mem_image.mpr ⟨u,hy,θ.apply_symm_apply x⟩,fun i hi=>?_⟩; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; apply (neighbors_mem ..).2
  rw [show x=θ u from (θ.apply_symm_apply x).symm, show separation (θ u) (θ k)=separation u k from ?_] -- lemma
  exact (neighbors_mem ..).mp (hz hk)
  change separation (p.1.1.act u+p.1.2) (p.1.1.act k+p.1.2)=_; rw [separation_translate,separation_signed]
end apo
section pact
variable (I Ξ n₀) (p':BudgetPoint) (χ)
include I Ξ n₀ χ p'
variable (β γ:ℝ) (k:ℕ)
lemma tuneships (x:Site c) (V:Config G c) : Poetry.echoing I Ξ n₀ χ k x V + Meadow.garner T.down T.low β γ B k x V=∑ i∈Poetry.bouquet I Ξ n₀ k, Meadow.share I p' x i * arena I χ β γ i V:= by
  unfold bouquet; rw [sum_disjSum, sum_map,sum_map]; dsimp only [Equiv.toEmbedding_apply]
  apply congr_arg₂ HAdd.hAdd
  · unfold echoing; rw [Finset.sum_filter]; apply sum_congr rfl; intro i hi
    let z:= i.val; let t:=stampP I Ξ z; let u:=(t.card:ℝ)⁻¹; let f:=stream I χ V (booths I Ξ n₀ i); simp only [arena]; change (if x∈ t then (-u)*f else 0)= (if x∈ t then u else 0)* ((-1:ℝ)*f); split <;> ring
  unfold garner; rw [Finset.sum_product]; dsimp only [Meadow.share,Sum.elim]; change _=∑ s:Seat c,∑ i∈_, (if (strings T.down p' (legs s i)).site=x then (1:ℝ) else 0) * arena I χ β γ (.inr (legs s i)) V
  rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ↓reduceIte]; rfl
lemma aster (x:Site c) : Poetry.barony n₀ I Ξ χ k β γ x= ∑ i∈Poetry.panel n₀ I Ξ k, Meadow.garnerAt I p' x i • ((gallery I χ β γ).logRead i) := by
  ext V; unfold barony Meadow.atlas; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; unfold likely; unfold panel; rw [sum_map,sum_product]; simp only [Equiv.toEmbedding_apply]; simp_rw [tuneships n₀ I χ Ξ p' β γ k]; rw [Finset.mul_sum] -- edit
  apply sum_congr rfl; intro θ _; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
  dsimp only [gallery,garnerAt,Function.comp_apply,smul_eq_mul]; rw [Equiv.apply_symm_apply]
  let q:= share I p' ((spin θ).symm x) i; let v:=arena I χ β γ i (θ.view V); change Rim c*(q*v)=q*(Rim c*v); ring
end pact
end YM.PhysicalNext.Repeat.Poetry
