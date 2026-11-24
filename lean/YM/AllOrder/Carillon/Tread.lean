import YM.AllOrder.High.Extract
import YM.AllOrder.Carillon.Coop
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Trimmings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir

/-!
# Repriced variant of High.Extract.
# Preservation of POINTWISE additive log including indicator partners

After support shifts of the general all-order stratum (Eber). One output basis
per step, all FAllowed; this will also work whenever the finite family chosen
(for the step under β, period etc) is paired to the others by Offers. Doesn't
apply mask merger yet. Generalizes first-order template.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Carillon
open High
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {k j m π : ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
local notation "B" => radiusB p
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)


open Trio Slide -- edit
variable (F:Finset H.fragrances) (χ:Chi) (p':BudgetPoint)
section ledgerT
variable {β γ t v:ℝ} (hp:Collection.Local (posting p' H) p' (organ H χ β γ) t v)
include hp
lemma sparedC (V:Config G c) :
    (posting p' H|>.read (organ H χ β γ)|>.additive p' V) = (Beam.marquee H p'|>.read (linger F χ k β γ)|>.additive p' V) +
       ∑ i∈foliage F k, masked p'.threshold ((Beam.marquee H p').reg i).support ((organ H χ β γ).logRead i) V:= by
  let t' i:= masked p'.threshold ((Beam.marquee H p').reg i).support ((organ H χ β γ).logRead i) V; let h i:=if i∈ foliage F k then t' i else 0
  let f i:= ((posting p' H).read (organ H χ β γ)).regularOccurrence p' i V; let g i:= ((Beam.marquee H p').read (linger F χ k β γ)).regularOccurrence p' i V
  have he : g=f-h:= by
    funext i; change masked _ _ ((linger F χ k β γ).logRead i) V=f i-h i; rw [newC_ledger]; have hh : f i=t' i:= by unfold t'; rw [Beam.rewrite_rule]; rfl
    rw [hh]; unfold h; split
    next hz=> rw [sub_self]; simp [masked]
    next hz=> rw [sub_zero]; rfl
  have hs: Summable f:= Roof.Embrasure.series _ _ hp V
  have h':HasSum h (∑ i∈ foliage F k,t' i):=by
    convert hasSum_sum_of_ne_finset_zero (s:= foliage F k) (f:=h) (fun i hi=> if_neg hi) using 1; exact sum_congr rfl fun i hi=> (if_pos hi).symm
    infer_instance
  have he': (∑' i, g i)= (∑' i, f i)-∑ i∈ foliage F k,t' i:= by rw [he]; exact (hs.hasSum.sub h').tsum_eq
  change (∑' i,f i)=(∑' i, g i)+_; rw [he',sub_add_cancel]
end ledgerT
section income
variable (β γ:ℝ) {Y:Stars→Side} {w r:ℕ} (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa:∀ i:Stars,Offer G (Y i)) (V:Config G c)
local notation "P₀" => (Beam.marquee H p')
local notation "h₀" => (organ H χ β γ)
local notation "h₁" => (linger F χ k β γ)
local notation "R₀" => foliage F k
local notation "f₀" => centerC F χ k β γ
def usedC (k:ℕ) (i:Site c) (V:Config G c):= ∑ x∈foliage F k, Meadow.garnerAt H p' i x *((P₀).read h₀|>.regularOccurrence p' x V)
variable (hBod:p'.B=Pressure.radiusB p) (hc0 : ∀ i∈F,∀ x∈perf H i,perf H i⊆neighbors r x) (hop : Pressure.radiusB p + Pressure.radiusB p ≤ r) (u:Site c)
include hc0 hop hBod
variable {sf c' : ℝ} (h : Collection.Local (posting p' H) p' (organ H χ β γ) sf c')
include h
open Boulevard
lemma liftsGC : ‖usedC F χ p' β γ k u V‖ ≤ (ballCost r:ℝ)*sf:= by
  obtain ⟨a,ha,hX⟩:= h.cheap
  let Z:= B; let P':= posting p' H; let f i:= masked p'.threshold (P'.reg i).support (((P₀).read (organ H χ β γ)).E i) V
  let R i:= Meadow.garnerAt H p' u i; have hv i : ((P₀).read h₀|>.regularOccurrence p' i V)= f i:= by change masked _ ((P₀).reg i).support _ _=_; rw [Beam.rewrite_rule]
  unfold usedC; simp_rw [hv]; apply le_trans (norm_sum_le ..)
  let s:= neighbors r u; let E i x:= if (P'.reg i).site=x then a i * Real.exp (preExponent p' * coverNumber p'.B (P'.reg i).support) else 0
  calc
    _ ≤ ∑ i∈ R₀, ∑ x∈s,E i x:= by
        apply sum_le_sum; intro i hi; have hp : 0≤∑ x∈s,E i x:=sum_nonneg fun x _=> (hX x).1 i
        change ‖R i*f i‖ ≤ _; by_cases ht:R i=0; · rw [ht,zero_mul,norm_zero]; exact hp
        have he:= (artists F p' hBod hc0 hop u i hi ht).2; rw [Beam.rewrite_rule] at he
        rw [norm_mul, Real.norm_of_nonneg (Meadow.nonnegative ..)]; apply (mul_le_of_le_one_left (norm_nonneg (f i)) (Meadow.portions ..)).trans; apply (CouplingShape.mask_cost (ha i) V).trans
        apply (le_mul_of_one_le_right (ha i|>.1) (Real.one_le_exp (show 0≤preExponent p' * coverNumber p'.B (P'.reg i).support from mul_nonneg (Song.headline p').exponent_pos.le (Nat.cast_nonneg _)))).trans;
        unfold E; rw [sum_ite_eq,if_pos (he (P'.reg i).anchor)]
    _ ≤ (ballCost r:ℝ)*sf:= by
        rw [sum_comm]; apply le_trans (sum_le_sum (fun x _=> budget_sum (hX x) R₀))
        rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) h.H_nonneg
lemma chamber_valueC (hU: flags p'.threshold V=∅): ‖f₀ u V‖ ≤ (ballCost r:ℝ)*sf:= by
  have he i : ((P₀).read h₀|>.regularOccurrence p' i V)=((h₀).logRead i) V:= masked_eq _ _ _ _ (by unfold Healthy; rw [hU]; simp)
  have hp:= liftsGC (k:=k) F χ p' β γ V hBod hc0 hop u h; unfold usedC at hp; simp_rw [he] at hp
  rw [(newC_bound_frame F χ p' β γ u), Finset.sum_apply]; exact hp
omit h
variable {l:ℕ} (hq : ∀ i,p'.Regular ((posting p' H).reg i).support ((organ H χ β γ).logRead i))
    (hP : ∀ i j, p'.Regular univ (fa i j))
include hq hP
omit hP in
lemma tidy_occasionC (he:r ≤ l): Tidy p' (neighbors l u) (usedC F χ p' β γ k u):= by
    refine tidy_sum _ _ R₀ _ fun i hi=> ?_; by_cases hB: Meadow.garnerAt H p' u i=0; · simp only [hB,zero_mul]; exact tidy_const ..
    refine tidy_scale _ _ (tidy_mask _ (X:=((P₀).reg i).support) ?_ ?_)
    · rw [Beam.rewrite_rule]; exact hq i
    intro j hj; apply (neighbors_mem ..).2; exact ((neighbors_mem ..).1 ((artists F p' hBod hc0 hop u i hi hB).2 hj)).trans he
end income
end YM.AllOrder.Carillon

