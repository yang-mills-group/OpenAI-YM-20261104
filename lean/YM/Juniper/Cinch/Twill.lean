import YM.Juniper.Cinch.Temple
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
open Quotes Finset Ovens Ovens.Pipes Progress.DirectedRecipe Payments Further.LogJets Pressure StressFlux
set_option quotPrecheck false
open scoped InnerProductSpace
variable {U : Pipes G c}{A B:Tap G c}{b δ v w τ σ : ℝ}(T:Pylon W c)

-- compensating clover on minimum extended address. spread through all signed origins to avoid chosen-wrap orientation requirement. POSE carries n²; already billed to ambiguity. use only output Π.Masks.
def husk (G:Gauge) {c:Side} (o:Site c) := counter (fun i j : PlaqAxes=> if i=j then 1 else 0) o (G:=G)
def twill (G:Gauge) {c:Side} (o:Site c)(δ:ℝ): Config G c→ℝ := (factor*δ) • husk G o
lemma twill_eq (o:Site c)(U:Config G c) (δ:ℝ): twill G o δ U=factor*δ * ((∑ i:PlaqAxes, ‖petals U o i‖^2)/2):=by
    simp [twill,husk,counter,VerifiedReset.quad,ite_mul]
lemma sit (s:Signed)(b y:Site c)(U:Config G c) (δ:ℝ): twill G y δ (pull s b U)=twill G (affine s b y) δ U:= by
   simp_rw [twill_eq, petals_moves, reframe_norm]; rw [Equiv.sum_comp _ (fun i=> ‖petals U (affine s b y) i‖^2)]
lemma prepare (k:Seat c): halo 2 {(k.2)} ⊆ k.spread T.corner:= by
   rw [← k.turn_zero, ← Finset.image_singleton, Push.Local.halo_map _ (Push.Local.turn_sep _ _)]; exact Finset.image_subset_image T.clap
namespace Pylon
-- one soft commutator per Seat. If original compact apex NOT healthy neither. Beware heads small-mask-only payoff.
def gap (δ:ℝ)(k:Seat c): Config G c→ℝ := twill G k.2 δ -- primary
-- δ in caller = delta(Y) - delta(actual)
def graft (δ:ℝ)(k:Seat c) := masked W.threshold (k.spread T.corner) (gap (G:=G) δ k)-masked W.threshold {k.2} (gap (G:=G) δ k)
abbrev map (k:Seat c):RegularAddress c:= ⟨k.2,k.spread T.corner,(k.reg T.corner T.az).anchor⟩
lemma charger (i:Seat c): W.Regular (T.map i).support (gap (G:=G) δ i):=
    CouplingShape.reg_extend (CouplingShape.reg_scale _ (counter_regular _ _ _)) (prepare T _)
lemma origin (i:Seat c): (gap (G:=G) δ i) 1=0:=by simp [gap,twill_eq]
lemma pays (x:Site c) (y: Signed) (k:Seat c) (t:ℝ): let i:= k.move y x -- note: dot notation order
    (T.map i).site=affine y x k.2∧ (T.map i).support=image (affine y x) (T.map k).support ∧ gap (G:=G) t i=(gap t k) ∘ pull y x ∧ graft T (G:=G) t i=(graft T t k) ∘ pull y x:= by
   intro i; have h:i.2= affine y x k.2:= rfl; have hv:i.spread T.corner=image (affine y x) (k.spread T.corner):= k.spread_move y x _; have hh:gap (G:=G) t i= gap t k ∘ pull y x:= funext fun V=> (Cinch.sit y x k.2 V t).symm
   refine ⟨h,hv,hh,funext fun u=> ?_⟩; unfold graft; simp only [Function.comp_apply,Pi.sub_apply]; rw [hv,h,hh,← Finset.image_singleton]; exact congrArg₂ (·-·) (congr_fun (Seat.distribute (x:=(y,x)) ..) _) (congr_fun (Seat.distribute (x:=(y,x)) ..) _)
lemma tender (i:Seat c) (t:ℝ): let f:= graft T (G:=G) t i; Trio.Tidy W (T.map i).support f ∧ ∀ V, f V≠0 → ¬Healthy W.threshold (T.map i).support V:= by
   intro f; have hp : ({i.2}:Finset (Site c)) ⊆ (T.map i).support:= Finset.singleton_subset_iff.mpr (T.map i).anchor; have hg:=(T.charger (δ:=t) (G:=G) i)
   -- mask_small used by stake cannot use tidy_mask for singleton support. payload not local! prove manually
   let g:= gap (G:=G) t i; let S:= (T.map i).support; let p:Finset (Site c):={i.2}; let u:=masked W.threshold p g
   refine ⟨Trio.tidy_sub W (Trio.tidy_mask W hg (Finset.Subset.refl _)) (show Trio.Tidy W S u from ?_),?_⟩
   · refine ⟨fun V Z ht hv=> ?_, masked_measurable _ _ _ hg.borel,CouplingShape.stencil_gi hg.symmetry _ _⟩; have hi:Healthy W.threshold p V=Healthy W.threshold p Z:= VerifiedReset.healthy_reads _ p S hp V Z ht hv
     by_cases h:Healthy W.threshold p V
     · exact (masked_eq _ _ _ _ h).trans ((hg.sites _ _ ht).trans (masked_eq _ _ _ _ (hi ▸ h)).symm)
     exact (masked_ne _ _ _ _ h).trans (masked_ne _ _ _ _ (hi ▸ h)).symm
   intro V h he; apply h; change masked _ S g V - masked _ p g V=0; rw [masked_eq _ _ _ _ he, masked_eq _ _ _ _ (VerifiedReset.healthy_mono hp he), sub_self]

def headBill (G:Gauge) (P:BudgetPoint) := (Fintype.card PlaqAxes:ℝ)*pairBill G P*P.threshold^2
def droop (G:Gauge) (P:BudgetPoint) (δ:ℝ) := |δ| *headBill G P
lemma vessel (t:ℝ)(k:Seat c): W.supBounds k.2 (T.map k).support (gap (G:=G) t k) (droop G W t) ∧ ∀ V:Config G c, ‖graft T t k V‖≤ droop G W t:= by
   let b:=headBill G W; let s:=droop G W t; let S:= (T.map k).support
   have ht:= pair_nonneg G W; have hy:= W.threshold_pos
   have hY: Bill W k.2 (Healthy W.threshold {k.2}) b (husk G k.2):= by
      refine Bill.le (counter_bill ..) ?_; unfold b headBill; simp_rw [abs_ite, abs_one, abs_zero, ite_mul,zero_mul,one_mul, Finset.sum_ite_eq,Finset.mem_univ, if_true]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) (Fintype.card PlaqAxes)) ht) (sq_nonneg W.threshold)]
   have hs : Bill W k.2 (Healthy W.threshold {k.2}) s (gap (G:=G) t k):= by
      refine Bill.le (Bill.scale (factor*t) hY) ?_; unfold s droop; rw [abs_mul,abs_of_pos factor_pos]; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) factor_le) hY.nonneg
   have hp : ({k.2}:Finset (Site c)) ⊆ S:= Finset.singleton_subset_iff.mpr (T.map k).anchor
   refine ⟨Bill.sup hs (fun _ h=> VerifiedReset.healthy_mono hp h),fun V=> ?_⟩
   by_cases he:graft T t k V=0
   · rw [he,norm_zero]; exact hs.nonneg
   change ‖masked W.threshold S (gap t k) V-masked W.threshold {k.2} (gap t k) V‖ ≤ s; rw [masked_ne _ _ _ _ ((tender T k t).2 V he),zero_sub,norm_neg]
   by_cases ht:Healthy W.threshold {k.2} V
   · rw [masked_eq _ _ _ _ ht]; exact Bill.norm hs (l:=[]) (by simp) (by simp) ht
   rw [masked_ne _ _ _ _ ht,norm_zero]; exact hs.nonneg

lemma wires (t:ℝ)(V:Config G c): (∑ k:Seat c, masked W.threshold (T.map k).support (gap t k) V)- (∑ k:Seat c,graft T t k V)=t*∑ i:Site c, heads W i V:= by
    let f (i:Site c):= heads W i V
    have he k: masked W.threshold (T.map k).support (gap t k) V-graft T t k V= factor*(t*f k.2):= by
       change masked W.threshold (k.spread T.corner) (gap t k) V- (_- masked W.threshold {k.2} (gap t k) V)= factor * (t * heads W _ V); rw [sub_sub_cancel]
       by_cases hp: Healthy W.threshold {k.2} V; · rw [heads,masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hp,gap,twill_eq,mul_assoc]
       rw [heads,masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,mul_zero,mul_zero]
    rw [←sum_sub_distrib]; simp_rw [he, ←Finset.mul_sum]; rw [Fintype.sum_prod_type]; dsimp only; rw [Finset.sum_const, card_univ,nsmul_eq_mul]; unfold f; rw [mul_left_comm, ← mul_assoc factor (Fintype.card Signed:ℝ),factor_card,one_mul]
end Pylon
end YM.Juniper.Cinch
