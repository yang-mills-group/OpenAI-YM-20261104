import YM.LocalLTE.Pond.Wages
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
local notation "η"=>p.supportExponent
variable (α Δ)
-- second soft record high GR. at post.Tap.K sign: total exp(- masked) same => soft += NEW masked - OLD.
abbrev freshly   (R:PathData G) (i:Spikes n) := High.fresh R i.2 0 (factor*α) (factor*Δ) ∘ Seat.view i.1 -- P unused
variable (p R)
abbrev Cl (i:Spikes n):= Price.freshly Δ α R i
def remises (i:Spikes n) := masked p.threshold (Price.ridge R p i).support (freshly Δ α R i)- masked p.threshold (highEntry G R i).support (freshly Δ α R i)
abbrev changed (i:Spikes n) := i.2.length R < p.B
def unitH (p:BudgetPoint)(R:PathData G)(α Δ:ℝ)(i:Spikes n) := if changed p R i then 2*Price.Hret p R α Δ i else 0 -- argument order?
lemma total {ι γ:Type*}(Y:Finset ι)(f:ι→γ→ℝ)(g:ι→ℝ) (he:∀ i∈Y,SumBudget (f i) (g i)): SumBudget (fun i=>∑ y∈Y,f y i) (∑ y∈Y,g y) := by
    induction Y using Finset.induction with
    | empty=> simp [SumBudget]
    | insert i Y hi ih=> simp_rw [Finset.sum_insert hi]; exact budget_plus (he i (mem_insert_self ..)) (ih fun j hj=> he j (mem_insert_of_mem hj))
lemma climbZ (p:BudgetPoint)(R:PathData G)(i:Spikes n) : (highEntry G R i).support⊆(Price.ridge R p i).support:= Finset.image_subset_image (Price.erect R p _ _)
-- cost soft per ball. Declaration order problem hR uses p R shadow. isolate
-- permit Upper. infer helpers.
lemma hillZero (i:Spikes n) (h:¬changed p R i) : remises Δ α p R i=0:= by
   unfold remises; rw [show (Price.ridge R p i).support=(highEntry G R i).support from congr_arg (Seat.spread i.1) (if_neg h),sub_self] -- syntax order
lemma stationH (i:Spikes n) (h: changed p R i): (Price.ridge R p i).support=neighbors (2*p.B) i.1.2:= by
   rw [show (Price.ridge R p i).support=i.1.spread (neighbors (2*p.B) 0) from congr_arg (Seat.spread i.1) (if_pos h)]; apply Scarf.normRange; simp [Lattice.affine]
include hR
lemma tending (i:Spikes n) : Trio.Tidy p (Price.ridge R p i).support (Price.remises Δ α p R i) ∧ (∀ U, Price.remises Δ α p R i U≠0→ ¬Healthy p.threshold (Price.ridge R p i).support U) ∧ ∀ U, ‖Price.remises Δ α p R i U‖≤ Price.unitH p R α Δ i:=by
    let f:=freshly Δ α R i; let X:= (highEntry G R i).support; let Y:= (Price.ridge R p i).support
    let u:=X; have h:p.Regular X f := Seat.regular i.1 (High.fresh_regular R i.2 (0:Site n) hR p (factor*α) (factor*Δ))
    have hx:=Price.climbZ p R i
    have hp : p.Regular Y f:= reg_larger h hx; refine ⟨Trio.tidy_sub p (Trio.tidy_mask _ hp (Finset.Subset.refl _)) (Trio.tidy_mask _ h hx),fun U hu h=> hu (?_),fun U=>?_⟩
    · unfold remises; rw [Pi.sub_apply,masked_eq _ _ _ _ h,masked_eq _ _ _ _ (healthy_mono hx h),sub_self]
    let Z:=Hret p R α Δ i; have hv:p.supBounds i.1.2 X f Z := by
      let Δ₀:= turnFee p; apply VerifiedReset.sup_le (i.1.sup (High.fresh_regular R i.2 (0:Site n) hR p (factor*α) (factor*Δ)) (Bill.sup (High.fresh_bill ..) (fun _ he=>he))) ?_
      change Δ₀ * (|factor*α+factor*Δ| * (High.price R i.2 p*p.threshold^3)) ≤ Z; unfold Z Hret; rw [← mul_add,abs_mul,abs_of_pos factor_pos]; have ht:=mul_le_of_le_one_left (abs_nonneg (α+Δ)) factor_le; linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (mul_nonneg (High.price_nn R i.2 p) (pow_nonneg p.threshold_pos.le 3))) (turnFee_pos p|>.le)] -- edit
    unfold unitH; split
    next h=> exact (norm_sub_le ..).trans ((add_le_add (CouplingShape.mask_cost (VerifiedReset.sup_larger hv hx) _) (CouplingShape.mask_cost hv _)).trans_eq (by rw [two_mul]))
    next h=> rw [Price.hillZero Δ α p R i h]; simp
omit hR
private lemma summ (i:Spikes n) (_ht:0 ≤ |α+Δ|) : 0 ≤ Price.unitH p R α Δ i:=by
    unfold unitH Hret; have h:=High.price_nn R i.2 p; have hs:=p.threshold_pos; have ht:=turnFee_pos p; split_ifs <;> positivity
lemma atop (i:Spikes n) : 0≤ Price.unitH p R α Δ i:= Price.summ Δ α p R i (abs_nonneg _)
-- Costs across anchors.
def lofty (p:BudgetPoint)(G: Gauge)(σ C α Δ:ℝ):= ((ballCost (2*p.B) :ℝ)* (2*(turnFee p*(|α+Δ| * p.threshold^3)) * highBase G p σ C))*Real.exp ((p.supportExponent+1)*ballCost 2)
include hR hv
lemma torrid : Ac.Hit (n:=n) (fun i:Spikes n=>(Price.ridge R p i).support) p.B (Price.unitH p R α Δ) (η+1) (Price.lofty p G σ C' α Δ):=by
    let u:=unitH p R α Δ (n:=n); have he i:0 ≤ u i:= Price.atop ..
    let a:= (2*(turnFee p*(|α+Δ| * p.threshold^3))); let b:=highBase G p σ C'; let z:=Real.exp ((p.supportExponent+1)*ballCost 2)
    have hA:0≤a:=by unfold a; have h:=turnFee_pos p; have he:=p.threshold_pos; positivity
    have hk: anchored p (highEntry G R) u (a*b):=by
       intro i; have hh:= Quotes.anchored_scale hA (rows (n:=n) _ _ _ _ hR hv|>.2.1) i; refine budget_mono hh (fun i=> ?_) ?_
       · split; next => exact mul_nonneg (Real.exp_nonneg _) (he _)
         exact le_rfl
       intro j; split
       next h=>
           refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _); unfold u unitH; split; next h=> unfold Hret a; exact le_of_eq (by ring)
           exact mul_nonneg hA (High.price_nn R j.2 p)
       exact le_rfl
    have hp : ∀ i:Site n, SumBudget (fun j:Spikes n=> if j.1.2=i then u j else 0) (a*b) := by
       intro i; refine budget_mono (hk i) (fun i=>?_) ?_
       · split; exact he _; exact le_rfl
       intro j; change _ ≤ (if j.1.2=i then _ else _); split; exact p.loMass _ _ (he j); exact le_rfl
    have hy:0≤ a*b:=budget_nonneg (hp 0)
    intro i; let Y:=neighbors (2*p.B) i; let f k (j:Spikes n):= if j.1.2=k then u j else 0; let g j:=∑ k∈Y, f k j; let D:=(∑ k∈Y, a*b)
    have hG: SumBudget g D:= Price.total (Y) f (fun _ => a*b) (fun i _=> hp i) -- edit
    refine budget_loosen (budget_mono (budget_scale (Real.exp_nonneg (x:=(p.supportExponent+1)*ballCost 2)) hG) (fun x=> ?_) ?_) ?_
    · split; next h=> exact mul_nonneg (he _) (Real.exp_nonneg _)
      exact le_rfl
    · intro x; dsimp only; have ht:0≤g x:=hG.1 _; split
      next h=>
        by_cases hx':changed p R x; swap; · rw [unitH,if_neg hx',zero_mul]; exact mul_nonneg (Real.exp_nonneg _) ht
        rw [Price.stationH p R x hx'] at h ⊢
        have hx:x.1.2∈Y:= (neighbors_mem ..).2 ((separation_comm ..).trans_le ((neighbors_mem ..).1 h))
        have he' : u x = g x:= by unfold g f; rw [Finset.sum_eq_single_of_mem x.1.2 hx (fun j hj hp => if_neg (Ne.symm hp)),if_pos rfl]
        rw [mul_comm _ (Real.exp _),← he']; apply mul_le_mul_of_nonneg_right _ (he _); refine Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ (by have he:=p.exponent_pos; linarith)); exact_mod_cast Scarf.standing (2*p.B) p 2 x.1.2 le_rfl
      exact mul_nonneg (Real.exp_nonneg _) ht
    unfold D lofty; rw [Finset.sum_const,nsmul_eq_mul,mul_comm]; apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _); exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) hy
end YM.AnalyticBridge.VerifiedReset.Collection.Price
