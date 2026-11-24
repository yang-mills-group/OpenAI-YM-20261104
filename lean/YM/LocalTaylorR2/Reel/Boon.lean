import YM.LocalTaylorR2.Reel.Strand
import YM.LocalTaylorR2.Reel.Barium
import YM.LocalTaylorR2.Capstone.Lens
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Brim
open Progress.DirectedRecipe
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
open YM.RG01.Survive Port Candle
/-! # Sterner prices despite recalibration -/
section budget
variable {A:ℕ→RegularAddress c}{B:BudgetPoint} {z v u:Scroll G c} {e k:ℝ}
lemma budgetF (h:Meadow.Budget B A z e)(ha:e≤k): Meadow.Budget B A z k:= by obtain ⟨w,h,hp⟩:=h; exact ⟨w,fun i=>budget_loosen (h i) ha,hp⟩
lemma gauges_scale (h:Meadow.Budget B A z e)(w:ℝ): Meadow.Budget B A (w • z) (|w| *e):=by
   obtain ⟨u,h,hp⟩:=h; refine ⟨(fun i=>|w| *u i),fun i=>?_, fun i=>⟨CouplingShape.reg_scale _ (hp i).1,CouplingShape.sup_scale _ (hp i).2⟩⟩
   convert! (budget_scale (abs_nonneg w) (h i)) using 1; ext j; dsimp only; split <;> ring
lemma gauges_sub (h:Meadow.Budget B A z e)(hp:Meadow.Budget B A v k): Meadow.Budget B A (z-v) (e+k):= Capstone.meadow_sub h hp (by abel)
lemma gauges_add (h:Meadow.Budget B A z e)(hp:Meadow.Budget B A v k): Meadow.Budget B A (z+v) (e+k):= by simpa using! gauges_sub h (gauges_scale hp (-1))
lemma cash_zero (B:BudgetPoint)(A:ℕ→RegularAddress c): Meadow.Budget B A (G:=G) 0 0:=
   ⟨fun _=>0,fun i=>by simp [SumBudget],fun i=> ⟨CouplingShape.reg_const (p:=B) (G:=G) 0,no_cost ..⟩⟩
variable {ι: Type*}
lemma gauges_sum (Z:Finset ι)(f:ι→ Scroll G c)(s:ι→ℝ)(hp:∀ i∈Z,Meadow.Budget B A (f i) (s i)):Meadow.Budget B A (∑ i∈Z,f i) (∑ i∈Z,s i):= by
   induction Z using Finset.induction_on with
   | empty => rw [sum_empty,sum_empty]; exact cash_zero ..
   | insert i Z hi ih=> rw [sum_insert hi,sum_insert hi]; exact gauges_add (hp i (mem_insert_self ..)) (ih fun _ hj=> hp _ (mem_insert_of_mem hj))
lemma reenact (F:ℕ→Prop)(h:Meadow.Budget B A z e): Meadow.Budget B A (fun i=> if F i then z i else 0) e:= by
   obtain ⟨g,h,hp⟩:=h; refine ⟨g,h,fun i=>?_⟩; dsimp only; split; exact hp _; exact ⟨CouplingShape.reg_const _,sup_le (no_cost ..) (hp i).2.1⟩
lemma resCopy (h:Meadow.Budget B A z e)(hp:Meadow.Budget B A v k) (he:∀ i V, Healthy B.threshold (A i).support V→memo V (z i) = memo V (v i)): Meadow.Budget B A v e:= by
   obtain ⟨k,h,hB⟩:=h; obtain ⟨g,_,hp⟩:=hp; refine ⟨k,h,fun i=> ⟨(hp i).1,(hB i).2.1, fun V hx y hy ht=>?_⟩⟩
   rw [← LocalGaussian.identical ((line_eq ..).mp (he i V hx)) y]; exact (hB i).2.2 V hx y hy ht
variable (f:Strand→Scroll G c){m:ℕ}(h:∀ q,Meadow.Budget B A (f q) e)
variable (q:Strand)(G₀:∀ i V,Healthy B.threshold (A i).support V→ Filled ⊤ m Strand.dial (fun t=>memo V (f t i)))
include h G₀
lemma pursues [Fintype ι] (w:ι→ Strand)(x:ι→ℝ) (hx:∑ i, |x i| ≤ k)
    (hi:∀ (U:Config G c)(a:Strand→ Still U), Filled ⊤ m Strand.dial a → a q-a Strand.bud=∑ i,x i • a (w i)): Meadow.Budget B A (f q-f Strand.bud) (k*e):= by
   let X i:= x i • f (w i); have he:0≤e:= by obtain ⟨a,h,-⟩:=h q; exact budget_nonneg (h 0)
   refine budgetF (resCopy (gauges_sum univ X (fun i=> |x i| * e) (fun i _=> gauges_scale (h _) _)) (gauges_sub (h _) (h Strand.bud)) ?_) ((Finset.sum_mul ..).symm.trans_le (mul_le_mul_of_nonneg_right hx he))
   intro i V hv; unfold X; simp only [Finset.sum_apply,Pi.smul_apply,Pi.sub_apply,map_sub,map_sum,memoScale]; exact (hi V _ (G₀ i V hv)).symm
end budget

abbrev mergePoly (p:ℕ) (i:ℕ): Prop:= 3≤ i ∧ ¬p+1 ≤ i
lemma segmentsAt {M:ℕ}(take f g:ℕ→Prop)(y:Expansions H M)(p:H.fragrances)
    (he:∀ i,take i↔ f i ∨ g i)(hp:∀ i, f i → ¬ g i) :
    fullSegments (fun _ k=>take k) y p=fullSegments (fun _ k=>f k) y p+fullSegments (fun _ k=>g k) y p:= by
      ext V
      unfold fullSegments; dsimp only [Pi.add_apply]; rw [← mul_add]
      apply congr_arg; rw [← Finset.sum_union ?_]; swap
      · rw [Finset.disjoint_left]; exact fun i hi hi'=> hp _ ((mem_filter.mp hi).2) ((mem_filter.mp hi').2)
      congr! 1; ext x; simp [he]
lemma separated (p:ℕ)(χ:Chi)(γ:ℝ)(E:Scroll G f)(T:Alliance I H 1 0)(hp:2≤p): sight H E T χ γ p true (fun i=>¬p+1≤ i)=
    sight H E T χ γ p true (fun i=>¬ 3 ≤ i)+ sight H E T χ γ p false (mergePoly p):= by
      let F:=sight H E T χ γ p; let v:=crawl H E T χ γ p
      have he : v true (fun i=>¬ p+1 ≤ i)= v true (fun i=> ¬3 ≤ i) + v false (mergePoly p):=by
         ext1 i; rcases i with i|i <;> unfold v crawl; swap; · simp
         rw [Pi.add_apply,Sum.elim_inl,Sum.elim_inl,Sum.elim_inl,segmentsAt H _ _ _ _ _ (he:=fun i=> ?_) (hp:=fun i _ _=>?_), smul_add]
         all_goals unfold mergePoly at *; omega
      funext i U; change Rim c * v _ _ _ _=Rim c*v true _ _ _ + Rim c*v false _ _ _; rw [he]; exact mul_add ..
end YM.LocalTaylorR2.Reel
