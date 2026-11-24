import YM.AllOrder.High.Low
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Duet

/-!
# Up/down routing of whole young clusters

Torus-cut ports: matcher pairs on local Molecules (not just one amplitude),
spanning both complete footprints. Finset chosen separately per account. Use
nonempty supports in the seam read, even if the integrated amount turns out
zero. Apply later both to pure and to modeled tickets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {S':StepData C F} {T:Tube G S} {T':Tube G S'} {R : RG.Rep G f} {R' : RG.Rep G F} {H : Cash W p a L X o U T R} {I: Cash W p a L X o V T' R'}

section strand
variable (Γ α : ℕ) (G : Finset H.ThinP)
def live (u : H.fragrances) : Prop := u.1 ≤ Γ ∧ (∀ i, u.2 i∈G) ∧ coefficient H.seam u.2≠0

def strands : Finset H.fragrances := ((Finset.range (Γ+1)).sigma (fun i=> Fintype.piFinset (fun _j : Option (Fin i)=> G))).filter fun p=> coefficient H.seam p.2≠0 -- type
lemma runIn (u : H.fragrances) : u∈strands Γ G ↔ live Γ G u:= by unfold strands live; simp [Fintype.mem_piFinset, and_assoc]

abbrev Upper (v r:ℕ) := ∀ i∈ G, coverNumber r (H.smallAt i) ≤ v

def clusterBound (a b Γ:ℕ) := ((Γ+1)*a)*(4*b+2)+2*b
lemma runs_small {v r : ℕ} (p : Upper G v r) (i : H.fragrances) (h:live Γ G i) : coverNumber r (perf H i) ≤ (Γ+1)*v := by
  -- analogous to Meadow.wages
  have hx:= connected_pay H.seam H.smallAt r H.testS i.2 zero_le_one h.2.2; unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx; have hv j: (coverNumber r (H.smallAt (i.2 j)):ℝ) ≤ v:= by exact_mod_cast p _ (h.2.1 j)
  have hy:(coverNumber r (perf H i):ℝ)≤(Γ+1)*v := by
    refine le_trans hx ((Finset.sum_le_sum (fun i _=> hv i)).trans ?_)
    rw [sum_const,nsmul_eq_mul]; simp only [card_univ,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    exact mul_le_mul_of_nonneg_right (by gcongr; exact h.1) (Nat.cast_nonneg _)
  exact_mod_cast hy
lemma hall (v r:ℕ) (p:Upper G v r) (i: H.fragrances) (h:live Γ G i) {x:Site c} (hx : x∈perf H i) : perf H i⊆ neighbors (clusterBound v r Γ) x:=
    fun _ hy => (neighbors_mem ..).mpr ((Corona.extent _ r hx hy).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (runs_small Γ G p i h)) _)) -- plus right? Lean weird
end strand

section correspondence
variable (f' : Site C → Site c) (U : Finset H.ThinP) (V:Finset I.ThinP)
    (χ : Chi) (x:Site C)
    (A : Config G C) (B: Config G c) {d d':ℕ}

/-- correspondence *at x*. Only required to transport the lives stratum.
The two neighborhoods can use slack on the common large-torus side. Analytic
continuity across β (or terms across moving period families) not required. -/
structure ExchangeP (d d':ℕ) where
  relates : I.ThinP → H.ThinP → Prop
  maps i : i∈V → I.smallAt i ⊆ neighbors d x → ∃ j∈U, relates i j
  wins j : j∈U → H.smallAt j⊆neighbors d (f' x) → ∃ i∈V, I.smallAt i⊆ neighbors d' x ∧ relates i j
  singular {i j k} : relates i j → relates i k → j=k
  distinctive {i j k} : I.smallAt i⊆neighbors d' x→I.smallAt k⊆neighbors d' x→ relates i j→ relates k j→i=k
  thick {i j} : relates i j → H.smallAt j = (I.smallAt i).image f'
  amount {i j} : relates i j → I.spawn χ A i.val= H.spawn χ B j.val

variable {f' U V χ x A B}
variable (P' : ExchangeP f' U V χ x A B d d') {u : I.fragrances} {v : H.fragrances}
local notation "p'" => P'

lemma strand_sub (u : I.fragrances) (i) : I.smallAt (u.2 i) ⊆ perf I u := Finset.subset_biUnion_of_mem (I.smallAt ∘ u.2) (mem_univ _)
include P'

section paired
variable {n:ℕ} {p : Option (Fin n) → I.ThinP} {q : Option (Fin n) → H.ThinP}
    (h : ∀ i,P'.relates (p i) (q i))
include h
lemma image_ticket : perf H ⟨n,q⟩=(perf I ⟨n,p⟩).image f':= by
  ext i; simp only [perf,unionOf, Function.comp_apply, mem_image,mem_biUnion]
  constructor
  · rintro ⟨j,-,hj⟩; rw [P'.thick (h j)] at hj; obtain ⟨y,hY,rfl⟩:= mem_image.mp hj; exact ⟨_,⟨_,mem_univ j,hY⟩,rfl⟩
  rintro ⟨y,⟨j,-,hj⟩,rfl⟩; refine ⟨j,mem_univ _, (P'.thick (h j)).symm ▸ mem_image_of_mem _ hj⟩

variable (hf : Set.InjOn f' (neighbors d' x)) (hp : ∀ i, I.smallAt (p i) ⊆ neighbors d' x)
include hf hp
lemma coeff_port : coefficient I.seam p=coefficient H.seam q:= by
  apply Meadow.movement; intro i j; apply or_congr
  · exact ⟨fun he=> P'.singular (h i) (he.symm ▸ h j),fun he=> P'.distinctive (hp i) (hp j) (h i) (he.symm ▸ h j)⟩
  unfold Ac.meets; rw [P'.thick (h j),P'.thick (h i)]; constructor
  · rintro ⟨y,hb,ht⟩; exact ⟨_,mem_image_of_mem _ hb,mem_image_of_mem _ ht⟩
  rintro ⟨y,hy,h'⟩; obtain ⟨k,hk,hV⟩:= mem_image.mp hy; obtain ⟨j',hj,hh⟩:= mem_image.mp h'
  exact ⟨k,hk, ((hf (show j'∈neighbors d' x from hp j hj) (show k∈neighbors d' x from hp i hk) (hh.trans hV.symm)) : j'=k) ▸ hj⟩

lemma mass_port : I.trainedPool χ A ⟨n,p⟩= H.trainedPool χ B ⟨n,q⟩ := by
  unfold Cash.trainedPool Gas.term; dsimp only; rw [coeff_port P' h hf hp]; congr! 2; exact prod_congr rfl fun i _=> P'.amount (h i) -- check
end paired

def Arrival (r:ℕ) (U:Finset H.ThinP) (x:Site c) := (strands r U).filter (fun u=>x∈ perf H u)
def risk (H : Cash W p a L X o g T R) (f: H.fragrances) (V:Config G c) (χ:Chi):= -((Song.perf H f).card:ℝ)⁻¹ * H.trainedPool χ V f

variable {Γ a₀ b₀:ℕ} (h : Upper U a₀ b₀) (hh' : Upper V a₀ b₀) (hf : Set.InjOn f' (neighbors d' x))
    (hg : clusterBound a₀ b₀ Γ ≤ d) (hj : d ≤ d')
-- explicit includes? p' etc

lemma sumshares (Γ : ℕ) (a₀ b₀ : ℕ) (h : Upper U a₀ b₀) (hh' : Upper V a₀ b₀)
    (hf : Set.InjOn f' (neighbors d' x)) (hg : clusterBound a₀ b₀ Γ ≤ d) (hj:d≤d') :
    ∑ i∈Arrival Γ V x, risk I i A χ = ∑ j∈Arrival Γ U (f' x), risk H j B χ := by
  let S' := Arrival Γ V x; let Y:= Arrival Γ U (f' x)
  have hd {c:Side} (x:Site c) {a b:ℕ} (h:a≤b): neighbors a x ⊆ neighbors b x := fun _ hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans h)
  have hv {v} (hi:v∈ S') : perf I v⊆ neighbors d x := (hall Γ V a₀ b₀ hh' v ((runIn ..).1 (mem_filter.mp hi).1) (mem_filter.mp hi).2).trans (hd x hg)
  have hu {v} (hi:v∈ Y): perf H v⊆ neighbors d (f' x):= (hall Γ U a₀ b₀ h v ((runIn ..).1 (mem_filter.mp hi).1) (mem_filter.mp hi).2).trans (hd (f' x) hg)
  have hx {p:I.fragrances} (hh:p∈ S') i:= (strand_sub p i).trans (hv hh); have ha {p:I.fragrances} (hh:p∈S') i:=(hx hh i).trans (hd x hj)
  choose R hR hY using fun (p:I.fragrances) (hh:p∈S') i=> P'.maps (p.2 i) (((runIn ..).1 (mem_filter.mp hh).1).2.1 i) (hx hh i) -- edit
  let f (p:I.fragrances) (hh:p∈S'):H.fragrances:= ⟨p.fst, R p hh⟩
  apply Finset.sum_bij f (fun p hh=>?_) (fun p hi q hq he=> ?_) (fun v hv'=>?_) (fun i hi=> ?_)
  · apply mem_filter.mpr; rw [runIn]; have he := (runIn ..).1 (mem_filter.mp hh).1; refine ⟨⟨he.1, hR p hh, coeff_port P' (hY p hh) hf (ha hh) ▸ he.2.2⟩,?_⟩
    rw [show perf H (f p hh)=_ from image_ticket P' (hY p hh)]
    exact mem_image_of_mem _ (mem_filter.mp hh).2
  · rcases p with ⟨n,p⟩; rcases q with ⟨m,q⟩; change Sigma.mk n _=Sigma.mk m _ at he; obtain rfl:n=m:=congr_arg Sigma.fst he
    injection he with he h'; congr 1; funext i; exact P'.distinctive (ha hi i) (ha hq i) (hY _ hi i) ((congr_fun h' i).symm ▸ hY _ hq i)
  · have hU:= (runIn ..).1 (mem_filter.mp hv').1
    choose p hp he hQ using fun i=> P'.wins (v.2 i) (hU.2.1 i) ((strand_sub v i).trans (hu hv')); let u:I.fragrances:=⟨v.fst,p⟩
    have hy:live Γ V u:= ⟨hU.1, hp, (coeff_port P' hQ hf he).symm ▸ hU.2.2⟩
    have hh: u∈S':= by
      apply mem_filter.mpr; refine ⟨(runIn ..).2 hy,?_⟩
      have ht:= image_ticket P' hQ; change perf H v=_ at ht; have hz : f' x∈ (perf I u).image f':= ht ▸ (mem_filter.mp hv').2; obtain ⟨y,hp',hd⟩:= mem_image.mp hz
      have h' : y=x:= hf (show y∈neighbors d' x from (by obtain ⟨i,-,hi⟩ := mem_biUnion.mp hp'; exact he i hi)) (show x∈neighbors d' x from (neighbors_mem ..).2 (by simp)) hd; exact h' ▸ hp'
    refine ⟨u,hh,?_⟩; unfold f; congr 1; exact funext fun i=> P'.singular (hY u hh i) (hQ i)
  let V:= hY i hi; unfold risk; rw [show I.trainedPool χ A i=_ from mass_port P' V hf (ha hi),show perf H (f i hi)=_ from image_ticket P' V,card_image_of_injOn (hf.mono (Finset.coe_subset.mpr ((hv hi).trans (hd x hj))))]
end correspondence
end YM.AllOrder.High
