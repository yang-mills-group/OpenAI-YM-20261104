import YM.Qlocal.Gauges.Rigger
/-! Preparing the canonical currency for both before- & after-Loans.
 Keeper. Marker posture.Poss.Count & Registration proof. Phi geometry reads from Story.Act.Key variant with stencil cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Gauges.Lamp
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload YM.Qlocal.Gauges.Atlas
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Reckoner Parabola
open RGComparison01 RGComparison01.Pledge Quipu Quipu.Sonnet Atlas Planet
open Footprint
variable {Ω ι J V I : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n c:Side}{P: RG.Rep G n}
    {o:V→Site n}{s s':V→Support n}{q:R.Mode→ℝ}{a b v t δ C A B θ ρ ζ:ℝ}
    {Y:Taste Ω o P R}{dcl:Set (ℕ ×ℕ)}
variable (X:Lamp R Ω P o)
set_option quotPrecheck false
local notation "B!" => Live o R X.census
local notation "S₀" => Stakeup R o s X.census
local notation "D₀"=> Payload.deck R s
variable {x:Ω} {h₁:RetainsDeclared dcl Y s} {h₀:Peak P o Y q P.p.supportExponent δ δ}
    (hp:Payload.Fabric h₁ h₀ x)(f:Ω→ Senses R→ℂ)(L: HasSlots P.p P.activities)
    (p:Rental q) (hz:0<δ) (hv:1 ≤ v) [Fintype V]
local notation "X'"=> (X.roster_ hp f L)
local notation "f₀"=> intoK R s o X.census
local notation "q★"=> slate R s
local notation "v'"=> Revenue.compile q v δ s (o:=o) (k:=X.census)
noncomputable abbrev archetype (p:RG.Rep G n)(m:ℕ)(a t:ℝ):= t⁻¹*(4+Real.exp p.p.supportExponent * m*a) 
include p hv hz
local notation "A*"=> (Fintype.card (Senses R))
lemma rentPh (hy:0≤A)(hf:∀ j,X.cost j≤ A) : Bench (fun i=>(X.roster_ hp f L x i).M) (Revenue.compile q v δ s (o:=o) (k:=X.census)) (archetype P (Fintype.card (Senses R)) A v):= by
 let w:= v'; have hv' :0< v⁻¹:=inv_pos.mpr (zero_lt_one.trans_le hv); let k := v⁻¹/δ; have hK : 0 < k:= div_pos hv' hz; have hW:∀ i:S₀,0 < w i:=fun i=> Revenue.rising p hz hv (f₀ i); let M(i):=(X' x i).M
 obtain ⟨o',hx,hσ,hG⟩:= Provisional.bench hp rfl p.pos hK L x;
 let Y(i:B!):=o (Sonnet.root i.val); let ℓ: S₀→Site n:= Sum.elim o' Y;
 refine ⟨ℓ,fun i=>?_,fun i=>(hW i).le,fun i=>?_⟩
 · rcases i with i|i; exact hx _; change Y i∈ (X.bits x i.val).crest; rw [X.gate]; exact halo_subset _ _ (mem_singleton_self _)
 let h(j:S₀):=if ℓ j=i then w j*(M j).weight * Real.exp (P.p.supportExponent*coverNumber P.p.B (M j).crest) else 0; have hh(j:S₀):0≤h j:=by unfold h; split; exact mul_nonneg (mul_nonneg (hW _).le (Leaf.profit _)) (Real.exp_nonneg _); rfl
 let α:= Real.exp P.p.supportExponent; let α':= v⁻¹ * α * A; change SumBudget h _; let y(i:Senses R):= X.cost i

 · refine budget_finite hh ?_; unfold Stakeup; change ∑ j: D₀ ⊕ B!,h j≤ v⁻¹*(4+ Real.exp P.p.supportExponent*Fintype.card (Senses R)*A); rw [Fintype.sum_sum_type];
   have hl: (∑ j:D₀,h (.inl j))≤ v⁻¹*4:= (budget_sum (hG i) univ).trans_eq (by change v⁻¹/δ *_=_; field_simp; ring) -- requires hz
   have hh : ∀ j:B!,h (.inr j) ≤ α':= by
      intro j; unfold h; split; swap; · unfold α' α; positivity
      change v⁻¹*(X.bits x j.val).weight * _≤ _; rw [X.weight, show (M (.inr j)).crest= _ from X.gate x j.val]; have hv : coverNumber P.p.B (Tale.court P.p.B (Y j)) ≤1:= Vase.halo_cost _; have hg x i: 0≤ X.cost i:= (X.priority x i).safe; unfold α' α; rw [mul_right_comm v⁻¹]; apply mul_le_mul; rotate_left -- simplify eager?
      · exact hf _
      · exact hg x j.val
      · exact mul_nonneg hv'.le (Real.exp_nonneg _)
      refine mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_of_le_one_right P.p.exponent_pos.le ?_)) hv'.le; exact_mod_cast hv
   have ht: (∑ i:B!,h (.inr i)) ≤ Fintype.card (Senses R)*α':= ((sum_le_sum (g:=fun _=>α') (fun i _=>hh i)).trans ?_); swap; · simp only [sum_const,nsmul_eq_mul,Finset.card_univ]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_le_of_injective (living o R X.census) (living o R X.census).injective)) (by unfold α' α; positivity) -- edit
   apply le_trans (add_le_add hl ht); unfold α'; unfold α; apply le_of_eq; ring
 -- hy binder
-- true root geometry list for ancestor
namespace Span
omit p hz hv
local notation "Y0"=> Senses R
local notation "Ω'"=> Loft R s
open StageArt
def specification(g:Ratio c n)(W:V→Support n)(i:Loft R W):= (slate R W i).val.biUnion (StageArt.fly g ∘ W)
variable (H:StepData c n) -- Foot arguments.Geometrical projections independent δ++
local notation "Xg"=> H.ratio.parent
lemma pins (H:StepData c n)(W:V→Support n)(i:Loft R W)(v:V)(he:v∈(slate R W i).val): StageArt.fly H.ratio (W v) ⊆ specification H.ratio W i:= subset_biUnion_of_mem (StageArt.fly H.ratio ∘ W) he
lemma contact (hq:∀ i,o i∈ s i)(i:Loft R s): (specification H.ratio s i).Nonempty := by obtain ⟨v,hv⟩:= hot0 (R:=R) (s:=s) i; exact ⟨_,(pins H s i v hv) (show Xg (o v) ∈_ from mem_image_of_mem _ (hq v))⟩
-- true leaf crest contains ALL stencil positions. Analyst COST requires short only. shape.Future Dat.X.Condition.
set_option quotPrecheck false
local notation "ζ!" => H.ratio
variable (hq: ∀ i:V,s i⊆Tale.court (P.p.B-X.census) (o i)) (hc':X.census≤P.p.B)
include h₁ h₀ hq hc'
lemma homeland (j:S₀): specification H.ratio s (f₀ j)⊆ StageArt.fly H.ratio (X' x j|>.M.crest):= by
 rcases j with j|j
 · let hV:= Payload.signs L hp|>.ink j; intro v hv; obtain ⟨z,hz,h⟩:= Finset.mem_biUnion.mp hv; exact Finset.image_subset_image (hV z hz) h
 intro v hv; obtain ⟨p,hp',ht⟩:= Finset.mem_biUnion.mp hv; apply Finset.image_subset_image ?_ ht; change s p⊆ (X.bits x j.val).crest; rw [X.gate]; exact (Tale.vestments _ _ _ (show Tale.Live o j.val X.census from j.prop) (fun i _=>hq i) hc' p hp') -- order
end Span
end YM.Qlocal.Gauges.Lamp
