import YM.LocalLTE.Tile.Bouquet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Reframe
/-! Local LTE high-order representation/compatibility on supported tiles. Adapts
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Reframe`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {J₀ M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
section petals
variable (I)
def panelN (J₀ k:ℕ) : Finset ℕ := (univ ×ˢ (Meadow.bouquetN I J₀ k)).map (pennant I).symm.toEmbedding
variable {k:ℕ}
lemma petaledN (i:ℕ) : i∈panelN I J₀ k ↔ (pennant I i).2∈Meadow.bouquetN I J₀ k:= by
  unfold panelN; simp only [mem_map_equiv,mem_product]; simp

end petals
section apo
variable (I) (p' : BudgetPoint) (x:Site c)
-- radius ℓ; purch post c
abbrev studioN (J₀ l b:ℕ) := roomSizeN J₀ l b + 2*b
local notation "D''" => Meadow.studioN J₀ X.halo B
lemma modestN (i: Magazine I) (hv: i∈Meadow.bouquetN I J₀ m) (hB:p'.B=B) (ht: share I p' x i≠0): x∈(Beam.contents I p' i).support ∧ (Beam.contents I p' i).support⊆ neighbors D'' x := by
  rcases i with i|i
  · obtain ⟨⟨z,hz⟩,hi,rfl⟩:= mem_map.mp (inl_mem_disjSum.mp hv)
    let z':=vintageN z hz; have he: x∈perf I z':= by contrapose! ht; exact if_neg ht
    change x∈(Beam.dashboard I z').support ∧ (Beam.dashboard I z').support ⊆_; rw [Beam.see]
    exact ⟨he, fun i hi=>(neighbors_mem ..).mpr (((neighbors_mem ..).1 (enteredN hz x he hi)).trans (Nat.le_add_right ..))⟩
  obtain ⟨⟨s,i'⟩,he,rfl⟩:=mem_map.mp (inr_mem_disjSum.mp hv); have hf : Meadow.melody T.down i'≤ B:= (mem_filter.mp ((mem_product.mp he).2)).2
  let k:= strings T.down p' (legs s i'); have he:k.site=x:= by contrapose! ht; exact if_neg ht
  change x∈k.support∧ k.support⊆_
  refine ⟨he ▸ k.anchor,?_⟩; rw [show x=s.2 from he.symm.trans (tunesAnchor ..)]; intro x hx; have h:= (neighbors_mem ..).1 (yarn T.down p' s i' hx); apply (neighbors_mem ..).2; dsimp only [Meadow.studioN]; omega
lemma assignedN (i:ℕ) (h : i∈Meadow.panelN I J₀ m) (hB:p'.B=B) (hp:garnerAt I p' x i≠0):x∈((Beam.marquee I p').reg i).support ∧ ((Beam.marquee I p').reg i).support⊆ neighbors D'' x:= by
  let p:=Song.pennant I i; let θ:=spin p.1; let u:=θ.symm x
  obtain ⟨hy,hz⟩:=modestN I p' u p.2 ((petaledN (J₀:=J₀) I i).1 h) hB hp
  change x∈ Finset.image θ _ ∧ Finset.image θ (Beam.contents I p' p.2).support⊆ _
  refine ⟨mem_image.mpr ⟨u,hy,θ.apply_symm_apply x⟩,fun i hi=>?_⟩; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; apply (neighbors_mem ..).2
  rw [show x=θ u from (θ.apply_symm_apply x).symm, show separation (θ u) (θ k)=separation u k from ?_] -- lemma
  exact (neighbors_mem ..).mp (hz hk)
  change separation (p.1.1.act u+p.1.2) (p.1.1.act k+p.1.2)=_; rw [separation_translate,separation_signed]
end apo
section pact
variable (p':BudgetPoint) (X' : Match.Alliance I H 1 0)
  (hp:R'.path=R.path) (he:I.supportP=H.supportP) (hz:X'.units=Equiv.refl _)
    (χ) (γ:ℝ) (k:ℕ)
include p' X' hp he hz χ γ
lemma tuneshipsN (x:Site c) (V:Config G c) : Meadow.echoingN J₀ H χ k x V + Meadow.garner T.down T.low R.beta γ B k x V=∑ i∈Meadow.bouquetN I J₀ k, Meadow.share I p' x i * opus I X' χ γ i V:= by
  let X:=firstBatchN (J₀:=J₀) hp he
  have h (i:PoetN J₀ I) : X i∈ Meadow.calendarN J₀ H k ↔ i∈Meadow.calendarN J₀ I k:= by rw [tunesN,tunesN]; rfl
  unfold bouquetN; rw [sum_disjSum, sum_map,sum_map]; dsimp only [Equiv.toEmbedding_apply]
  apply congr_arg₂ HAdd.hAdd
  · unfold echoingN; rw [Finset.sum_filter]; symm; refine Finset.sum_equiv X (fun i=> (h i).symm) ?_; intro i hi
    obtain ⟨z,hx⟩:= i; let i: PoetN J₀ I:=⟨z,hx⟩
    let w:=boothsN J₀ I i; have hx:(perf I w)= Meadow.pasture H (X i).val:= Eq.trans (reconnects I X' _) (by rw [identifiesN X' hp hz he]; rfl)
    let v:= X i
    change (if x∈ perf I w then _ else _) * ((-1:ℝ)*stream H χ V (X'.furrow w))=if x ∈ Meadow.pasture H v.val then -(Meadow.voteN v)*_ else _
    rw [show X'.furrow w= boothsN J₀ H v from identifiesN X' hp hz he i,hx]; split_ifs
    · change _= -(Meadow.voteN v)* stream H χ V (boothsN J₀ H v); simp only [voteN]; ring
    rw [zero_mul]
  unfold garner; rw [Finset.sum_product]; dsimp only [Meadow.share,Sum.elim]; change _=∑ s:Seat c,∑ i∈_, (if (strings T.down p' (legs s i)).site=x then (1:ℝ) else 0) * opus I X' χ γ (.inr (legs s i)) V
  rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ↓reduceIte]; rfl
lemma asterN (x:Site c) : Meadow.baronyN H J₀ χ k γ x= ∑ i∈Meadow.panelN I J₀ k, Meadow.garnerAt I p' x i • ((plusone I X' χ γ).logRead i) := by
  ext V; unfold baronyN atlas; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; unfold likely; unfold panelN; rw [sum_map,sum_product]; simp only [Equiv.toEmbedding_apply]; simp_rw [tuneshipsN χ p' X' hp he hz γ k]; rw [Finset.mul_sum] -- edit
  apply sum_congr rfl; intro θ _; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
  dsimp only [plusone,garnerAt,Function.comp_apply,smul_eq_mul]; rw [Equiv.apply_symm_apply]
  let q:= share I p' ((spin θ).symm x) i; let v:=opus I X' χ γ i (θ.view V); change Rim c*(q*v)=q*(Rim c*v); ring
end pact
end YM.PhysicalNext.Repeat.Meadow
