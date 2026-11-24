import YM.RemainderComparison.Fallow.Studio
/-!
# Logical singleton projection on the marker-conditioned expression

Keeper runs after Passion.Both. tilts. Literal `Source.Coefficient` in the actual header and kernel conventions. Keeps `ζ` operator tests normalized before bases, connects X to Pet.R and bound. Before conversion on different bases by RG04, use representation supplying THESE commitments. No assumption chosen χ in Region matches a final stable graph.Via β conversion eventual.Se.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Fallow
open Function Filter Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker Finset
open Solos Mosaic Verse Serif Flues WickReps Ethereal Jolt Lacuna Lobby Passion GridRenewal.Rain PhysicalNext.Repeat WardBin.Crest
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {α:Type*}{G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
variable [Fintype θ][DecidableEq θ](J:Census θ)
variable {i:θ}{D:ι→Finset θ}{z:ι→ Poly J}(X: Hol G) (F:Plane G n θ) (a:Audited Q)
local notation "L"=>F.visor i
set_option quotPrecheck false
local notation "F₀"=>(L).basis
local notation "τ"=> (L).sectionQ
local notation "o'"=>(L).origin
local notation "A" => Roll T R Z D
local notation "A₁"=> cash T p R Z F X SeatD.MaskType.exactM z D

-- Unit projection data. Before α layout tests as all marker packs.V No continuity α on arbitrary OFFMASK required. Need physical test evaluation before operator size. 
local notation "R₀" => players T R Z F D i
local notation "M"=>SeatD.MaskType.exactM
local notation "Wq" => salary T R Z J F z i
local notation "δp" => crowns T p R Z J X F a z i
local notation "Rφ" => kernels T p R Z J X F a z i
variable (hp:Passion.Oriented D J Z z)(he:F.exam i)
variable {σ b t e wA:ℝ}{l k:ℕ}
variable (h:Precepts T p R Z D σ b)(hr:AxisG p F X t l e) (hQ : Placed R F D)
variable (w:θ→ℝ) (x:players T R Z F D i)
local notation "Y₁"=> area T R Z F (D:=D)
local notation "Q₁" => PairAt T p R Z F X x.val a i
local notation "P" => p.threshold
variable (V:Rep G n) (r:ℕ→ Config G n →ℂ)(hκ: Lodge T p R Z F X SeatD.MaskType.exactM D wA) -- shadow w
open Progress.DirectedRecipe
-- raw lower f grant assumptions.Flow band & Forms
variable {c d' δ:ℝ} (κ':players T R Z F D i↪ℕ)
variable (hW : Serif.Chorus J w Z z k) (hv:V.p=p)
include h hr hQ hκ hW hp he hv
-- Assembles Mark.ENTRY.Keps. Include representative precision seam
local notation "mu"=> Fallow.music T p R Z J X F a r z i κ'
variable (U:Config G n)
omit [Fintype θ] in
lemma stage (ht:Summable (cash T p R Z F X SeatD.MaskType.exactM z D a U)) :
    Poly.part (∑' i:A,A₁ a U i) J.quiet=0 ∧ Poly.part (∑' i:A,A₁ a U i) (J.fire i)= (mu).exponentialEntry o' τ V U:=by
    rw [Poly.share ht,Poly.share ht]; obtain ⟨f,hf,hB⟩:= Fallow.merit T p R Z J X F h hr hQ w hW hκ (i:=i)
    let Ff (i':A):= (A₁ a U i').part; have hg : ∀ x',0≤f x':=fun i=>(hB i a).1.1; have hx:= Local.sumBudget_uncharge hg hf
    have hhp:= (sizeSum (F:=«F») δp (budget_mono hx (fun i=> size_nonneg ..) fun i=> (hB i a).2)).1
    let W : (F₀).Coeff →L[ℂ] ℂ := ((LinearMap.proj (R:=ℂ) (φ:=fun _ : Config G n=> ℂ) U) ∘ₗ Local.primary τ o' V.p.threshold).toContinuousLinearMap
    constructor; · refine Eq.trans (tsum_congr (g:=fun _:A=> (0:ℂ)) ?_) tsum_zero; intro i; unfold cash; rw [Poly.part_smul]; exact mul_eq_zero_of_right _ (Passion.positive hp _ i.val.prop)
    change (∑' x:A,Ff x (J.fire i)) = W ((mu).x)+ ∑' i, (mu).maskedTerm V i U
    have heq : V.p.threshold=p.threshold:= hv ▸ rfl
    let g i':= masked p.threshold (Y₁ (i':R₀).val) (Rφ i') U
    have hs : Summable g := hx.2.1.of_norm_bounded (fun x'=>?_) -- edit
    · have hr' : ∑' i,((mu).maskedTerm V i U)= ∑' j,g j :=by
         apply Progress.DirectedRecipe.transferred_sum κ'
         · intro i'; unfold Coefficient.maskedTerm; rw [show (mu).support (κ' i')= (Y₁ i'.val) from κ'.injective.extend_apply (fun (i:R₀)=> Y₁ i.val) (fun _=>{o'}) i',show (mu).regular (κ' i')= Rφ i' from Progress.DirectedRecipe.stuffed ..,heq]
         intro j hj; unfold Coefficient.maskedTerm; rw [show (mu).regular j=0 from Progress.DirectedRecipe.blank _ _ hj]; unfold masked; simp
      have hx' (i':R₀) : Ff i'.val (J.fire i) = W (δp i')+g i':=by
         have he:=voices (z:=z) T p R Z J X F a h hr U i'; refine he.trans ?_; unfold W; rw [heq]; rfl
      rw [hr',show (mu).x=∑' i':R₀,δp i' from rfl,W.map_tsum hhp,← (W.summable hhp).tsum_add hs]
      refine ((tsum_subtype_eq_of_support_subset (show Function.support (fun i'=>Ff i' (J.fire i))⊆ {i'| Ra T R Z F i'=some i} from ?_)).symm.trans (tsum_congr hx'))
      intro i' hi; by_contra hv; exact hi (extraP T p R Z J X F a hp he i' hv U)
    by_cases he' : Healthy p.threshold (Y₁ x'.val) U
    · rw [show g _ = _ from masked_eq _ _ _ _ he']; exact (hB _ a).1.2 U he' [] (Nat.zero_le _) (by simp)
    rw [show g _= _ from masked_ne _ _ _ _ he',norm_zero]; exact hg _
end YM.RemainderComparison.Fallow
