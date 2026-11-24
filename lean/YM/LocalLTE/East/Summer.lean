import YM.LocalLTE.East.Balcony
/-! Orbit radius inward. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
section
lemma indicatorPull {ι κ:Type*} {P:ι→Prop} (v:ι→ κ)(hy:Set.InjOn v {i| P i})(f:κ→ℝ)(h:SumBudget f V): SumBudget (fun i=> if P i then f (v i) else 0) V:=by
  apply budget_of_sum; · intro i; split; exact h.1 _; exact le_rfl
  intro s; rw [← Finset.sum_filter]; refine le_trans (le_of_eq ?_) (budget_sum h ((s.filter P).image v)); exact (Finset.sum_image (by intro i hi j hj; exact hy ((mem_filter.mp hi).2) ((mem_filter.mp hj).2))).symm
lemma censusHit {ι:Type*} [Fintype ι]{o:ι→Site c} (h: Census m o) (D: Finset (Site c)):SumBudget (fun i=> if o i∈D then (1:ℝ) else 0) (D.card*m):=by
  refine budget_finite (fun i=>by split<;>norm_num) ?_; rw [← sum_filter, Finset.sum_const,nsmul_eq_mul,mul_one]; exact_mod_cast h D
lemma censusNext {ι κ:Type*}[Fintype ι][DecidableEq ι] {s':κ→ι} {t:ι→Site c}(h : Census m t) {P:κ→ℝ} (he: ∀ i:ι, SumBudget (fun j=> if s' j=i then P j else 0) v) (hv : 0≤v) (D:Support c): SumBudget (fun j=> if (t ∘ s') j ∈ D then P j else 0) (v*(D.card*m)):=by
   let V i:= if t i∈D then v else 0
   refine budget_fiberwise (W:=V) s' (fun i=> ?_) (fun i T hT=> ?_) (?_)
   · split
     next h=> simpa using (he (s' i)).1 i
     rfl
   · unfold V; split_ifs with hi
     · apply le_trans (le_of_eq ?_) (budget_sum (he i) T); apply sum_congr rfl; intro x hx; simp [hT x hx,hi]
     exact (sum_eq_zero fun i hi'=> by simp only [Function.comp_apply,hT _ hi', if_neg hi]).le
   convert budget_scale hv (censusHit h D) using 2 with i
   dsimp only [V]; split <;> simp
lemma budget_seat {ι :Type*} {f:ι→ℝ} (h:SumBudget f V) (α:Type*)[Fintype α]: SumBudget (fun p:α→ι=>∏ j,f (p j)) (V^(Fintype.card α)):=by
  apply budget_of_sum (fun i=> prod_nonneg fun j _=> h.1 _)
  intro u; let S j:=u.image (fun i=> i j)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (t:=Fintype.piFinset S) (fun p hp=> Fintype.mem_piFinset.mpr (fun j=>mem_image_of_mem _ hp)) (fun p _ _=> prod_nonneg fun j _=>h.1 _)).trans ?_
  rw [← Finset.prod_univ_sum S (fun _=> f)] -- edit
  simpa only [prod_const,card_univ] using! prod_le_prod (fun i _=> sum_nonneg (fun i _=> h.1 _)) (fun i (_:i∈univ)=> budget_sum h (S i))
-- Finset ≤n branches using encodability at exactly v.
lemma budget_group {ι:Type*} {f:ι→ℝ} (h: SumBudget f V)(k:ℕ) : SumBudget (fun s:Finset ι=>if s.card=k then ∏ i∈s,f i else 0) (V^k):=by
   apply budget_of_sum (fun i=> by
      split; · exact prod_nonneg fun i _=>h.1 _
      exact le_rfl)
   intro s; rw [← sum_filter]; let u:=s.filter (fun i=>i.card=k); let e (i:↥u): Fin k≃ (↥i.val):=(Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact (mem_filter.mp i.property).2)).symm
   let v (i:↥u): Fin k→ι:= fun j => (e i j).val; have hx i : i.val=univ.image (v i):=by
      ext j; constructor
      · intro hj; obtain ⟨k,hk⟩:= (e i).surjective ⟨j,hj⟩; exact Finset.mem_image.mpr ⟨k,mem_univ _,congr_arg Subtype.val hk⟩
      intro hj; obtain ⟨k,hk,rfl⟩:= mem_image.mp hj; exact (e i k).property
   have hp:Injective v:= fun i j he=> Subtype.ext (by rw [hx i,hx j,he])
   have he:= budget_sum (budget_seat h (Fin k)) (univ.image v); rw [sum_image hp.injOn, Fintype.card_fin] at he
   rw [← sum_attach]; refine le_trans (le_of_eq ?_) he; apply sum_congr (by simp [u]); intro i _; rw [hx]; exact Finset.prod_image (Injective.injOn (Subtype.val_injective.comp (e i).injective))
def rack (V:ℝ) (n:ℕ) := ∑ i∈Finset.range (n+1),V^i
lemma budget_grace {ι:Type*} (n:ℕ) {f:ι→ℝ} (h:SumBudget f V) : SumBudget (fun v:Finset ι=>if v.card≤ n then ∏ i∈v, f i else 0) (rack V n):=by
  have h:= budget_over  -- edit
     (Finset.range (n+1)) _ _ (fun i _=> budget_group h i)
  convert h using 2 with i
  rw [Finset.sum_ite_eq]; simp
  rfl
end
end YM.PhysicalNext.Repeat.East
