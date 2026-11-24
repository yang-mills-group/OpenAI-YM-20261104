import YM.RG05Readout.Nuclear.Samples
/-! Exact on discrete petals at finite radius with uniform tail funds.
 Center complexity solely by C' through whole support.Frontier ν_t adapter if
 derivative weights transported.Factorization lives regardless of Y.Z launch.
 No density comparison here.Application uses Tissue.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Lattice
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type}[TopologicalSpace E]
variable {V J:Type}[Fintype V][DecidableEq V]
local notation "U"=>Cloud V
local notation "W"=> Wave V
set_option quotPrecheck false
variable (s:V→ℕ)(Ω:Set E)(C:Allow V)(F:E→Wave V)
local notation "D!"=> ∑ i:V,(s i+2)
local notation "N"=>4*Fintype.card V
variable (S r:ℝ) (T: Finset (Cloud V))
-- recursive cumulative.Arity earnings
abbrev sky (r:ℝ)(k:ℕ):= r*(1/2:ℝ)^k
lemma sky_next (i:ℕ): sky r (i+1)=sky r i / 2:=by unfold sky; rw [pow_succ]; ring
lemma sky_open(i:ℕ)(hr:0<r): 0<sky r i:=by unfold sky; positivity
lemma sky_stop (i:ℕ)(hr:0<r):sky r i≤ r:=mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))
lemma sky_zero : Tendsto (sky r) atTop (𝓝 0):=by
    convert! (tendsto_const_nhds (x:=r)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num: (0:ℝ)≤ 1/2) (by norm_num)) using 1; rw [mul_zero]
noncomputable def restage (d k:ℕ) : E→Wave V := ∑ i∈ Finset.range k, stepQ F d S (sky r i) (sky r (i+1))
omit [TopologicalSpace E] in
lemma evolves (hr:0<r)(k d:ℕ) (x:E)(a:U)(ha:‖a‖< S) : (restage F S r d k x+originalQ F d S r x).val a=(originalQ F d S (sky r k) x).val a:=by
    induction k with
    | zero=> unfold restage sky; simp
    | succ k ih=>
        let Z:=restage F S r d k; rw [show restage F S r d (k+1)= Z+stepQ F d S (sky r k) (sky r (k+1)) from Finset.sum_range_succ .., Pi.add_apply, add_right_comm,AddMemClass.coe_add,Pi.add_apply]; rw [show (Z x+_).val a= _ from ih, step_glove F d _ _ _ a x ha (sky_open _ _ hr) (by rw [sky_next]; linarith only [sky_open r k hr])]; abel -- edit
section global
variable {C' x₀:ℝ}(h:Stone d Ω F)(hφ:Plant Ω C F x₀)(hd:∀ u∈Ω, Tall (F u) (d+1) 1 C')(hc:0≤C')(hrP:2*r≤ x₀)(hr:0<r)(hx:r≤1)(hp:(∑ i:V,(s i+2)) +4*Fintype.card V< d+1)(hs:0≤S)
include h hφ hd hc hrP hr hx hp hs
lemma spun (l:ℕ): Bouquet s Ω C (restage F S r d l) (redeem s d S*(2*r)*C'):=by
    let K:= redeem s d S; let g(i):= K*sky r i*C'; apply (Bouquet.sum (Finset.range l) g (F:=fun k=>stepQ F d S (sky r k) (sky r (k+1))) ?_).permit (fun _ _=> rfl)
    swap
    · intro i _; have h₁:=sky_open r i hr; have h₂:= sky_stop r i hr
      exact step_cap s Ω C F C' x₀ h hc hφ _ _ _ (sky_open r (i+1) hr) (by rw [sky_next]; linarith only [h₁]) (by rw [sky_next]; linarith) (by linarith only [h₂,hrP]) (h₂.trans hx) hs hd hp
    unfold g; rw [← Finset.sum_mul,← Finset.mul_sum]; apply mul_le_mul_of_nonneg_right _ hc; apply mul_le_mul_of_nonneg_left _ (redeem_pos s d S hs)
    have he(l:ℕ): (∑ i∈ Finset.range l, sky r i) + 2*sky r l=2*r:=by induction l with | zero=> simp [sky]; | succ i ih=> rw [Finset.sum_range_succ,sky_next]; linarith only [ih]
    linarith only [he l, sky_open r l hr]
lemma full_stencil (hT:∀ x∈T, ‖x‖< S) :
    ∃ G, Bouquet s Ω C G ((redeem s d S*2+1)*r*C')∧∀ u:E,∀ a∈T,∀ k≤d,pie (G u+ originalQ F d S r u) (F u) k a:=by
    let P:=(plot V 16).card; let b₀:=pellets s d 4
    have ht: ∀ᶠ k in atTop, ((T.card:ℝ)*P*b₀)*sky r k<r:=by simpa only [mul_zero] using (((sky_zero r).const_mul ((T.card:ℝ)*P*b₀)).eventually (gt_mem_nhds (by rwa [mul_zero])))
    have hN:∀ᶠ k in atTop,∀ x∈T,∀ y∈T,x≠y→2*sky r k< ‖x-y‖:=T.eventually_all.mpr fun x hi => T.eventually_all.mpr fun y _=> by by_cases hp:x=y; exact Eventually.of_forall fun k h=> (h hp).elim; apply ((sky_zero r).const_mul 2).eventually (gt_mem_nhds (show 2*0<‖x-y‖ from by rw [mul_zero]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hp))) |>.mono; intro k hk _; exact hk
    obtain ⟨k,hC,hN⟩:= (ht.and hN).exists; let t:=sky r k; let X:= striker F T S t d; let Y:= restage F S r d k
    have htP:= sky_open r k hr; have he':= sky_stop r k hr; have hX:=striker_cost s Ω C F T S t d h hφ hd hc (le_trans (mul_le_mul_of_nonneg_left he' zero_le_two) hrP) htP (he'.trans hx) (by omega)
    refine ⟨X+Y,(hX.add (spun s Ω C F S r h hφ hd hc hrP hr hx hp hs k)).permit (fun _ _=>rfl) ?_,fun u a ha n hn=>?_⟩
    · linarith only [show (T.card:ℝ)* (plot V 16).card * pellets s d 4 * t*C' ≤ r*C' from mul_le_mul_of_nonneg_right hC.le hc]
    let f:= originalQ F d S r u; let f':=originalQ F d S t u
    have ht: (X u+(Y u+f)).val =ᶠ[𝓝 a] (X u+f').val:=by
        filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds (hT a ha))] with x hx; exact congr_arg ((X u).val x+·) (evolves F S r hr k d u _ hx)
    unfold pie; rw [Pi.add_apply, add_assoc]; exact ((ht.iteratedFDeriv ℝ n).eq_of_nhds).trans (strike F T S t a _ u htP hT hN ha n hn)
lemma vitality (hT:∀ x∈T,‖x‖< S): ∃ G, Bouquet s Ω C G ((mintBase s S d * r⁻¹^(D!+N)+(redeem s d S*2+1)*r)*C')∧∀ u:E,∀ x∈T,∀ k≤d,pie (G u) (F u) k x:=by
   obtain ⟨G,hG,hE⟩:= full_stencil s Ω C F S r T h hφ hd hc hrP hr hx hp hs hT
   have hP:=original_cap s Ω C F C' _ h hc hφ r S hr hx hrP hs (fun i hi j hj=> hd i hi j (by omega)); let K:=originalQ F d S r
   refine ⟨G+K,?_ ,hE⟩; apply (hG.add hP).permit (fun _ _=>rfl); exact le_of_eq (by ring)
end global
end YM.RG05Readout.Nuclear
