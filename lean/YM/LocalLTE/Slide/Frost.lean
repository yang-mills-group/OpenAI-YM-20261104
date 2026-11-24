import YM.LocalLTE.Slide.Ice
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace YM.PhysicalNext.Repeat.Scarf
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Push.BetaTransport Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {X : Listing G c} {m r j k p:ℕ} {e d a Z K q b v Y : ℝ} {x:ℝ} {S:Set ℝ} {ι:Type}
section
variable [DecidableEq ι](E:ι→ RegularAddress c) (s:Finset ι)(m:ℕ)
    (B:BudgetPoint)
def delay (f:ι→ Config G c→ℝ) (i:Site c) (U:Config G c):= ∑ j∈s with (E j).site=i,(masked B.threshold (E j).support (f j) U-masked B.threshold (neighbors m i) (f j) U)
variable (f:ι→ Config G c→ℝ)
local notation "Λ" => delay E s m B
local notation "ra"=>enlarged E s m
lemma delayed (U:Config G c) (h:Summable (fun i=> masked B.threshold (E i).support (f i) U))(hP: Summable fun i=> masked B.threshold ((ra i).support) (f i) U) :
    ∑' i,masked B.threshold (E i).support (f i) U=(∑' i, masked B.threshold (ra i).support (f i) U)+∑ i, Λ f i U:=by
       let F i:=masked B.threshold (E i).support (f i) U; let R i:=masked B.threshold (ra i).support (f i) U; let v i:=F i-R i
       apply sub_eq_zero.mp; change (∑' i,F i)-((∑' i,R i)+_)=_; rw [← sub_sub, ← h.tsum_sub hP,sub_eq_zero]; change (∑' i,v i)=_; rw [tsum_eq_sum (s:=s) (hf:= -- edit
         ?_)]
       · let g i:= (E i).site
         have hh j: Λ f j U = ∑ i∈s with g i=j, v i:= Finset.sum_congr rfl (fun i hi => by
            obtain ⟨hi,hj⟩:= mem_filter.mp hi; change (E i).site=j at hj; unfold v R F Scarf.enlarged; rw [if_pos hi,← hj])
         rw [← sum_fiberwise_of_maps_to (t:=Finset.univ) (g:=g) (fun i (_:i∈s)=> Finset.mem_univ _) v]; simp_rw [hh]
       intro i hi; unfold v R F Scarf.enlarged; rw [if_neg hi,sub_self]
-- failure trace. Bore, Tidy
section
variable {A:ℕ} (h: Rooms E s m B A)
    (hs: ∀ i∈s, B.Regular (E i).support (f i))
include hs h
lemma sap (i: Site c) : Trio.Tidy B (neighbors m i) (Λ f i) ∧ ∀ V:Config G c,Healthy B.threshold (neighbors m i) V→ Λ f i V=0:=by
    let X:=s.filter (fun j=>(E j).site=i)
    have hx j (he : j∈X) : (E j).support ⊆ neighbors m i := (mem_filter.mp he).2 ▸ h.places j (mem_filter.mp he).1
    refine ⟨Trio.tidy_sum B _ X _ (fun j hj=> Trio.tidy_sub B (Trio.tidy_mask _ (hs _ (mem_filter.mp hj).1) (hx _ hj)) (Trio.tidy_mask _ (VerifiedReset.reg_larger (hs _ (mem_filter.mp hj).1) (hx _ hj)) (Finset.Subset.refl _))), fun V he=> Finset.sum_eq_zero (fun j hj=> ?_)⟩
    rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (AnalyticBridge.VerifiedReset.healthy_mono
       (hx _ hj) he),sub_self]
omit hs
lemma sap_cost {w:ι→ℝ} (i:Site c) (hv:∀ i∈s, B.supBounds (E i).site (E i).support (f i) (w i)) (hk: ∀ x, SumBudget (fun i=> if (E i).site=x then w i else 0) a) (V:Config G c): ‖Λ f i V‖ ≤ 2*a:=by
   let X:=s.filter (fun j=>(E j).site=i)
   refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun j=>2*w j) ?_) ?_)
   · intro j hj; obtain ⟨hi,hj⟩:= mem_filter.mp hj; refine (norm_sub_le ..).trans ?_; rw [two_mul,hj.symm]; exact add_le_add (CouplingShape.mask_cost (hv _ hi) _) (CouplingShape.mask_cost (VerifiedReset.sup_larger (hv _ hi) (h.places _ hi)) _)
   rw [← mul_sum]; gcongr; rw [sum_filter]; exact budget_sum (hk i) _
lemma flowSap (i:Site c){t:ℝ→ι→ Config G c→ℝ}{x:ℝ} {T:Set ℝ}(hp:x∈T) (ht:∀ i∈s,Shingle.Mild B (E i).support (fun k=> t k i) T) : Varies (fun k=> Λ (t k) i) x T:= by
    apply Mild.weighted; intro j hj; obtain ⟨hj,hq⟩:= mem_filter.mp hj; exact ((ht j hj).clipped x hp).sub (((ht j hj).mono (show _⊆ neighbors m i from hq ▸ h.places j hj)).clipped x hp)
end
-- no collisions.LOCK.STamp
lemma stanza {Y:ι→ℝ}{Z:BudgetPoint} (hk : Quotes.early Z E Y a)(hg:∀ i,0≤Y i) (x:Site c): SumBudget (fun i=> if (E i).site=x then Y i else 0) a:=by
    apply budget_mono (hk x)
    · intro i; split; next => exact hg _
      exact le_rfl
    intro i; split
    next h=> exact le_mul_of_one_le_right (hg _) (Real.one_le_exp (mul_nonneg (headline Z|>.exponent_pos.le) (Nat.cast_nonneg _)))
    rfl
end
end YM.PhysicalNext.Repeat.Scarf
