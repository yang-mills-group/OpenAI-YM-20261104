import YM.RG01Estimate.Society
/-!
 # Mini-budget for Rate requests on all short invoices after weak activation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Board
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext.Repeat Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Quotes Collection Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {S:StepData c f}{T:Tube G S} {K:Teller G}{X: ConnectedActivityE6.Target G K}
    {s a b y t v:ℝ}{o:Target.Order G s} {U:RG.Rep G f}

lemma fallow (p: ℕ)(he:∀ x,U.activities.E p x=0)(χ: Chi)(V:Config G c)(I:Cash s t a L X o y T U): stream I χ V (Brim.icon I p)=0 := by
  rw [Brim.lily]; unfold March.leaflet Pond.likely Stained.fringe
  have h U' : U.activities.regularOccurrence U.p p U'=0 := by simp only [Activities.regularOccurrence,masked,Set.indicator, he]; split<;> rfl
  have hx (F:Tree.Forest S.ratio) (Y:Coat T F) J z : Polar.floating Y o.a U s X.table z J X.halo (Brim.head p)=0 := by
    unfold Polar.floating Brim.head; rw [prod_singleton]; change Real.exp (-(U.activities.regularOccurrence _ p _) * _) -1= _; rw [h,neg_zero,zero_mul,Real.exp_zero,sub_self]
  have hv (F:Tree.Forest S.ratio) (Y:Coat T F): Shield.shelter Y s o.a (Brim.head p) U X.table X.halo=0 := by
    unfold Shield.shelter; split; next _=> unfold Shield.seating; simp only [Shield.bars,Pond.likely,hx,mul_zero,integral_zero,sum_const_zero]
    rfl
  simp only [Brim.once,hv,integral_zero,sum_const_zero,mul_zero]
lemma barren (E:Set ℕ)(he:∀ i∈E,U.activities.E i=0)(χ:Chi) (P:BudgetPoint) (z:ℝ)(I:Cash s t a L X o y T U): Single.Pays I P E χ z 0 ∧ Inherit.Debits U E 0 := by
   refine ⟨⟨⟨fun _=>0,?_,?_⟩⟩,?_⟩ -- typo
   · intro x; simp [SumBudget]
   · intro i hi hB; rw [show (fun V : Config G c=> stream I χ V (Brim.icon I i))=fun _=> 0 from funext fun x=> fallow i (fun V=>congr_fun (he i hi) V) χ x I]; exact sup_le (sup_const 0) (le_of_eq abs_zero)
   have hh i: (Inherit.selected U E).E i=0:= by by_cases h:i∈E <;> simp [Inherit.selected,h, he]
   refine ⟨fun _=>0,fun i=> ?_,fun x=>by simp [SumBudget,BudgetPoint.mass]⟩; rw [hh]; exact sup_le (sup_const 0) (le_of_eq abs_zero)

lemma cart (p: ℕ→ Config G c→ℝ) : Boulevard.throng p= Boulevard.throng (Caddy.righty p):= by
   let f:= Caddy.righty p
   funext x; symm
   have ht i : f (Caddy.e.symm (.inr i)) x=p i x:= by unfold f Caddy.righty Caddy.insertP; rw [Function.comp_apply, Caddy.e.apply_symm_apply]; rfl
   let j i:=Caddy.e.symm (.inr i)
   let g i:=p i x
   change (∑' i,f i x)=∑' i,g i
   refine tsum_eq_tsum_of_ne_zero_bij (fun i:support g=> j i.val) ((Caddy.e.symm.injective.comp Sum.inr_injective).comp Subtype.val_injective) ?_ (fun i=> ht i.val)
   intro i hy; cases h:Caddy.e i with
   | inr k=> have hs:j k=i:= Caddy.e.symm_apply_eq.mpr h.symm; exact ⟨⟨k,(show g k≠0 from by unfold g; rw [← ht,show Caddy.e.symm _=i from hs]; exact hy)⟩,hs⟩
   | inl k=> apply False.elim (hy ?_); unfold f Caddy.righty Caddy.insertP; dsimp only; rw [Function.comp_apply,h]; rfl
end YM.RG01Estimate.Board
