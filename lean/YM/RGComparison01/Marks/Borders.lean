import YM.RGComparison01.Marks.Diner
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
namespace Diner
open Lanes Foreman Checks Baked Palette Pillow Resin Season Ink Heron Switch Mallow Ovens OmitClusters Song Refrain Motion Luggage Oceanic Extra.Iteration
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Hoboken Stowe SliceRows
namespace Borders
open Driver
variable {i m Z k b:ℕ}
variable (M:ι→Lotus.Leaf R) (D:Driver M) (E:Ribbon R n)
variable [Fintype ι]
local notation "Zp"=> Diner.Driver.primary M D S
-- cumulative all roots at pre INTEGER exponent. λi/k_i comparison weights anchored, on PRIMARY ancestors (can pick first in crest). audience Mark. bounded. product keeps copies via temporary sold radii. need require works.Act.Model
variable (u:ι→ℝ) (V : Site c)
-- coarse regroup
omit [Fintype ι] in
lemma around (h:∀ i,0≤u i)(hx:∀ x:Site f, SumBudget (fun i=> if D.origin i=x then u i else 0) w)(X:Support c) : SumBudget (fun i=> if S.ratio.parent (D.origin i)∈ X then u i else 0) ((X.card*S.patch.L.val^4:ℕ)*w) := by
   let P:= Finset.univ.filter fun i=> S.ratio.parent i ∈ X; let b p i:= if D.origin i=p then u i else 0
   have hp : P.card ≤ X.card*S.patch.L.val^4:= Footprint.crowd S.ratio X
   have hg:= budget_over P _ _ fun i (_:i∈P)=> hx i; rw [sum_const,nsmul_eq_mul] at hg; apply budget_loosen (budget_mono hg ?_ ?_)
   · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hp) (budget_nonneg (hx 0))
   · intro i; split; exact h i; rfl
   intro i; split; next hv=> rw [Finset.sum_ite_eq, if_pos (show D.origin i∈P from mem_filter.mpr ⟨mem_univ _,hv⟩)]
   next=> exact hg.1 i
-- geometric product using elementary rescaling rather than exp of growing domain
variable {b0 : ℝ}
omit [Fintype ι] in
lemma shells (v : ι→ℝ)(hv : SumBudget v b0)(hB:0≤(b0:ℝ))(i:ℕ): SumBudget (fun s:Finset ι => if s.card≤ i then Stowe.dilation s v else 0) ((1+b0)^i*Real.exp 1):= by -- b0 binder
   let p:=1+b0; have hp:1 ≤ p:=by unfold p; linarith only [hB];
   let g k:= p⁻¹*v k; have hf := budget_scale (inv_nonneg.mpr (zero_le_one.trans hp)) hv
   have hz := AbsoluteSums.Product.set_products (budget_loosen hf (show p⁻¹ * b0 ≤ 1 from ?_)); swap
   · rw [inv_mul_le_iff₀ (zero_lt_one.trans_le hp),mul_one]; unfold p; linarith only
   apply budget_mono (f:=fun s=> p^i*Stowe.dilation s g) (budget_scale (pow_nonneg (zero_le_one.trans hp) i) hz)
   · intro i; split; exact prod_nonneg fun j _=> hv.1 _; exact le_rfl
   intro s; split
   next h=> apply (show Stowe.dilation s v=p^s.card*Stowe.dilation s g from ?_).trans_le (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp h) (prod_nonneg fun i _=> hf.1 i))
            unfold Stowe.dilation g; rw [Finset.prod_mul_distrib, ← mul_assoc, Finset.prod_const,← mul_pow,mul_inv_cancel₀ (zero_lt_one.trans_le hp|>.ne'),one_pow,one_mul]
   next=> exact mul_nonneg (pow_nonneg (zero_le_one.trans hp) _) (prod_nonneg fun i _=> hf.1 i)
-- output tariffs spent at H support cells for ANY full permutation mask/testing. REQUIRE Quick with root distances smaller than MORPH support.
variable (W:BudgetPoint)(w0 Y : ℕ)(α L₀ e b0:ℝ)
-- exposed argument order pre
abbrev sets (M : ι→ Lotus.Leaf R)(D:Driver M)(E: Ribbon R n)(S:StepData c f)(m Y:ℕ): Finset (Finset ι):=univ.filter (Quick M E D S m Y)
local notation "V'"=> Quick M E D S m Y
abbrev cashier (b0 v:ℝ)(l Y m : ℕ):= let z:= ((ballCost Y*l:ℕ):ℝ)*b0; (1+z)^m*Real.exp 1 * Real.exp v
omit [Fintype ι] in
lemma paid (h:∀ i,0≤u i)(hv : ∀ x:Site f, SumBudget (fun i=> if D.origin i=x then u i else 0) b0)(hx:0 ≤ α) (hp:∀ x : Site c,(coverNumber W.B (neighbors Z x):ℝ) ≤ L₀) : Ac.Hit (fun p: Finset ι=> neighbors Z (Zp p)) W.B (fun p=> if Quick M E D S m Y p then Stowe.dilation p u else 0) α (cashier b0 (α*L₀) (S.patch.L.val^4) (Z+Y) m):= by
   intro x; let X:= neighbors (Z+Y) x; let z:= (↑(ballCost (Z+Y)*S.patch.L.val^4:ℕ):ℝ)*b0
   let g i:= if S.ratio.parent (D.origin i)∈X then u i else 0
   have hg:= around M D u h hv (S:=S) X
   have hv₀:0 ≤ b0:= budget_nonneg (hv 0)
   have hp₀: SumBudget g z:= budget_loosen hg (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_right _ (neighbors_card _ _)) hv₀)
   have ht:= shells g hp₀ (budget_nonneg hp₀) m
   unfold cashier; dsimp only; rw [mul_comm _ (Real.exp _)]; refine budget_mono (budget_scale (Real.exp_nonneg (α*L₀)) ht) (fun i=>?_) (fun i=>?_)
   · split; next=> apply mul_nonneg; split; exact prod_nonneg fun i _=> h i; rfl; exact Real.exp_nonneg _
     exact le_rfl
   split; swap
   · exact budget_scale (Real.exp_nonneg (α*L₀)) ht|>.1 _
   next h'=>
     split; swap
     · rw [zero_mul]; exact budget_scale (Real.exp_nonneg (α*L₀)) ht|>.1 _
     next hs=>
       rw [if_pos hs.2.1,mul_comm (Real.exp _)]
       apply mul_le_mul ((le_of_eq ((Finset.prod_congr rfl ?_)))) (Real.exp_monotone (mul_le_mul_of_nonneg_left (hp _) hx)) (Real.exp_nonneg _) (prod_nonneg fun i _=> hp₀.1 i)
       intro j hj; refine Eq.symm (if_pos ((neighbors_mem ..).2 ?_));
       apply (separation_triangle x (Zp i) _).trans; rw [separation_comm x]; exact Nat.add_le_add ((neighbors_mem ..).1 h') ((neighbors_mem ..).1 ((hs.2.2 _ hj).2))
end Borders
end Diner
end YM.RGComparison01.Pledge
