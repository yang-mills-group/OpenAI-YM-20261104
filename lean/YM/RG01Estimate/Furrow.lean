import YM.RG01Estimate.Adjudge
/-!
 # A spatial-flat projection stamp with affine test exactly respected
 despite fixing Δ. Fully charged support. Only when canonical projection discrepancy
 has the extra `jury` margin (on these *representations*), not permitting storing
 arbitrary tiny but spatially slow e^natural in a remote germ!
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor
open Function Filter Set Lattice Wilson RG Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}(g:G.Simple)

structure Pilgrim (p : BudgetPoint) (n : Side) (hn:20<n.val) where
    X : Support n
    anchor : halo 2 {(0:Site n)} ⊆ X
    pays : coverNumber p.B X ≤ coin p n hn+81
    loops : ¬ Nonwrapping X 0
lemma pilgrim (hn:20<n.val) (hB:2 ≤ p.B) : Nonempty (Pilgrim p n hn):= by
    obtain ⟨a,hA,h'⟩:= left_min p n hn
    let b:Seat n:=⟨1,-a.site⟩
    let X:= expand a
    let c:RegularAddress n:= ⟨affine 1 (-a.site) a.site, a.support.image (affine 1 (-a.site)),Finset.mem_image_of_mem _ a.anchor⟩
    have he:b.spread X=expand c:= (expand_moves a c 1 (-a.site) rfl rfl).symm
    have ht:c.site=0:= by simp only [c,affine,Signed.act_one,add_neg_cancel];
    have hi:=Geo.enlarge p a hB; rw [h'] at hi
    refine ⟨⟨expand c,by rw [← ht]; exact Finset.subset_union_right,he ▸ (b.visit_count X).trans_le hi, fun h=> ?_⟩⟩
    refine hA ((spin_wrap 1 (-a.site) ..).mp ?_)
    change Nonwrapping (b.spread X) c.site; rwa [he,ht]

variable (p)(Δ:ℝ)
namespace Pilgrim
-- negative-log regular; Δ := D-delta local; pays +Δ*heads.
variable (G)
def toll (Δ:ℝ) (p:BudgetPoint) := |factor*Δ| * (2:ℝ)⁻¹ * (Fintype.card PlaqAxes) * (pairBill G p * p.threshold^2)
lemma toll_nn : 0 ≤ toll G Δ p := by have hp:=pair_nonneg G p; unfold toll; positivity
def warm (Δ:ℝ)(o:Site n) := counter (G:=G) (fun i j=> if i=j then -(factor*Δ) else 0) o
lemma valued (o:Site n) (U:Config G n): warm G Δ o U= -(factor*Δ)*((∑ i, ‖petals U o i‖ ^ 2) /2):= by
   unfold warm counter quad; simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ, ↓reduceIte, real_inner_self_eq_norm_sq,←Finset.mul_sum]; ring
lemma warmed (o : Site n): Bill p o (Healthy p.threshold {o}) (toll G Δ p) (warm G Δ o):= by
   have h:= counter_bill (G:=G) o (fun i j=> if i=j then -(factor*Δ) else 0) p
   apply Bill.le h (le_of_eq ?_); unfold toll; simp only [apply_ite abs,ite_mul,abs_zero,zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, abs_neg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
variable {p}{hn:20<n.val} (Q:Pilgrim p n hn) (V:Config G n)
lemma anchored : (0:Site n)∈Q.X:= Q.anchor (halo_subset _ _ (Finset.mem_singleton_self _)) -- param G unused
-- Wrap labels at all positions with orientations, plus separately paired mask at SAME footprint
-- retains E_noWrap demand. NONE in regular candidate; Oscar only.
def tea (x:Seat n) := warm G Δ 0 ∘ x.view
def frost (V:Config G n) := if Healthy p.threshold Q.X V then 0 else -masked p.threshold {(0:Site n)} (warm G Δ 0) V
def ice (x:Seat n) := frost G Δ Q ∘ x.view -- order check
include Q
lemma tea_pays (x:Seat n) : p.Regular (x.spread Q.X) (tea G Δ x) ∧ tea G Δ x (1:Config G n)=0 ∧ ¬ Nonwrapping (x.spread Q.X) x.2 ∧
   p.supBounds x.2 (x.spread Q.X) (tea G Δ x) (turnFee p*toll G Δ p):= by
    have h:p.Regular Q.X (warm G Δ 0):= reg_larger (counter_regular ..) Q.anchor
    refine ⟨x.regular h,?_,fun hx=> Q.loops (x.unwrapped hx), x.sup h (Bill.sup (warmed G p ..) (fun _ H=> healthy_mono (Finset.singleton_subset_iff.mpr (Q.anchored)) H))⟩
    unfold tea; rw [comp_apply,Seat.view,pull_one_field,valued]; simp
lemma faulted : frost G Δ Q V - masked p.threshold Q.X (warm G Δ 0) V= -masked p.threshold {(0:Site n)} (warm G Δ 0) V := by
    by_cases h: Healthy p.threshold Q.X V
    · rw [frost,if_pos h,masked_eq _ _ _ _ h,masked_eq _ _ _ _ (healthy_mono (Finset.singleton_subset_iff.mpr Q.anchored) h),zero_sub]
    rw [frost,if_neg h,masked_ne _ _ _ _ h,sub_zero]
lemma contract (x:Seat n) : GaugeInvariant (ice G Δ Q x) ∧ UsesFinal p.threshold (x.spread Q.X) (ice G Δ Q x) ∧
     Measurable (ice G Δ Q x) ∧ ∀ V:Config G n, ‖ice G Δ Q x V‖ ≤ toll G Δ p ∧ (ice G Δ Q x V≠0 → ¬ Healthy p.threshold (x.spread Q.X) V):=by
    have hj:p.Regular Q.X (warm G Δ 0):= reg_larger (counter_regular ..) Q.anchor
    have hh:GaugeInvariant (frost G Δ Q) := by
        intro k U
        have hp : Healthy p.threshold {(0:Site n)} (Lattice.gauge k U) = Healthy p.threshold {(0:Site n)} U:=by simp only [Healthy,gauge_flags]
        unfold frost; simp only [Healthy,gauge_flags]; split; rfl
        by_cases hK:Healthy p.threshold {(0:Site n)} U
        · rw [masked_eq _ _ _ _ (hp.mpr hK),masked_eq _ _ _ _ hK,hj.symmetry k U]
        rw [masked_ne _ _ _ _ (hp.symm ▸ hK),masked_ne _ _ _ _ hK]
    have ht:UsesFinal p.threshold Q.X (frost G Δ Q) :=by
       intro U V h hs; have hz:= healthy_reads p.threshold _ _ (Finset.singleton_subset_iff.mpr Q.anchored) U V h hs
       unfold frost; rw [healthy_reads p.threshold _ _ (Finset.Subset.refl _) U V h hs]; split; rfl
       by_cases hi: Healthy p.threshold {(0:Site n)} V
       · rw [masked_eq _ _ _ _ (hz.mpr hi),masked_eq _ _ _ _ hi,hj.sites U V h]
       rw [masked_ne _ _ _ _ (hz.symm ▸ hi), masked_ne _ _ _ _ hi]
    refine ⟨Push.Local.invariant_pull hh _ _,Push.Local.uses_pull ht _ _, (Measurable.ite (healthy_closed ..).measurableSet measurable_const ((masked_measurable _ _ _ hj.borel).neg)).comp (continuous_pull ..).measurable,fun V=> ?_⟩
    unfold ice Function.comp frost; split
    next h=> exact ⟨by rw [norm_zero]; apply toll_nn,by simp⟩
    next h=>
     refine ⟨?_,fun _=> mt (Seat.healthy ..).1 h⟩; rw [norm_neg]; by_cases hc:Healthy p.threshold {(0:Site n)} (x.view V)
     · rw [masked_eq _ _ _ _ hc]; exact Bill.norm (l:=[]) (warmed G p Δ 0) (by simp) (by simp) hc -- param order
     rw [masked_ne _ _ _ _ hc,norm_zero]; exact toll_nn ..
lemma head_pay : (∑ x:Seat n, ice G Δ Q x V) - (∑ x:Seat n, masked p.threshold (x.spread Q.X) (tea G Δ x) V)=Δ*(∑ i, heads p i V):= by
    have hp x : frost G Δ Q (Seat.view x V) - masked p.threshold (Seat.spread x Q.X) (tea G Δ x) V = factor*Δ*heads p x.2 V:=by
       rw [tea, Seat.distribute,comp_apply,faulted]; unfold heads
       have hz : Seat.spread x {0}={x.2}:= by unfold Seat.spread;simp [affine]
       by_cases hi: Healthy p.threshold {x.2} V
       · rw [masked_eq _ _ _ _ ((Seat.healthy ..).1 (hz.symm ▸ hi)), masked_eq _ _ _ _ hi, valued, Seat.view, petals_moves]; simp only [affine,Signed.act_zero,zero_add,reframe_norm]
         rw [Equiv.sum_comp (PlaqAxes.transform x.1) (fun i=> ‖petals V x.2 i‖^2)]; ring
       rw [masked_ne _ _ _ _ (by rw [← Seat.healthy,hz]; exact hi), masked_ne _ _ _ _ hi, mul_zero,neg_zero]
    rw [← Finset.sum_sub_distrib]; simp only [ice,comp_apply,hp,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,← mul_assoc]
    rw [show factor * Δ * ↑(Fintype.card Signed) = Δ from (by rw [mul_assoc,mul_comm Δ,← mul_assoc,factor_card,one_mul])]
end Pilgrim
end YM.RG01Estimate.Censor
