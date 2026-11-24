import YM.RGComparison.Core16.Forge.Charges
/-!
# All-periods purchased local excision
Critical: the energy loss on the adaptively chosen radius is measured before branch summation, but
comparison & probability AFTER summation. Not a claim tag admissibility is stable. No turned-free
outer variable in the shell price. This estimate loses NO power with the number of variables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge
open Filter Function Finset Lattice RG Tree Wilson MeasureTheory Push.AbsoluteSums.Animals
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {S : Side} {ι k T : Type} [Fintype ι] [Fintype k] [Fintype T]
variable {X:Prices} {B:Base G S ι k T}{g D : ℝ}
variable (loc:ι→Site S) (hX:Coverage X.K loc)
include hX in
lemma calm (x:Sky G ι) (j:ι) (r:ℝ)(H:nib x j≥r)(M:ℕ)
    (hM: 4*weights X (stride X M) < (1+incline X)^M*r ) : ∃ m∈range M, x∈riot loc (loc j) X r (stride X m) := by
   let z:=loc j; let E m:= threat loc z x (stride X m)
   have hn m : E m ≤ 4*weights X (stride X m):=by
      refine (sum_le_sum (f:=nib x) (g:=fun _=>4) (fun i _=>?_)).trans ?_
      · unfold nib; nlinarith only [G.chord_nonneg (x i),G.chord_le_two (x i)]
      rw [sum_const,nsmul_eq_mul,mul_comm 4]; gcongr; exact Nat.cast_le.mpr (price_cover hX ..)
   have h m:r ≤ E m:= H.trans (single_le_sum (fun i _=> Base.nib_nonneg x i) ((member ..).2 (by unfold z; simp)))
   by_contra! he
   have hj (m:ℕ)(hm:m<M): (1+incline X)*E m < E (m+1):=by
      refine lt_of_not_ge (fun hk=> he _ (mem_range.mpr hm) ⟨?_,h m⟩)
      rwa [←show stride X (m+1)= stride X m+X.b+X.b by unfold stride; ring]
   have hk:1<1+incline X:=(lt_add_iff_pos_right ..).2 incline_pos
   have ht m (hm:m≤M): (1+incline X)^m*r ≤ E m:=by
      induction m with
      | zero=> simpa only [pow_zero,one_mul] using h 0
      | succ m IH=> rw [pow_succ',mul_assoc]; exact (mul_le_mul_of_nonneg_left (IH (by omega)) (zero_le_one.trans hk.le)).trans ((hj m hm).le) -- m<M = hm
   exact (not_lt_of_ge ((ht M (le_refl _)).trans (hn _))) hM

omit [Fintype ι] in
lemma union_cost {α : Type*}{μ : Measure (Sky G ι)} (P : Finset α)(t:α→Set (Sky G ι))(h:∀i∈P, MeasurableSet (t i)) (V:Sky G ι→ℝ)(hW:Integrable V μ)(hV:∀x,0≤ V x) (W:Set (Sky G ι))(hm:MeasurableSet W)
    (he:∀ x∈W,∃ i∈P,x ∈ t i): (∫ x in W,V x ∂μ) ≤ ∑ i∈P,∫ x in t i, V x ∂μ:=by
    rw [← integral_indicator hm,sum_congr (s₁:=P) rfl (fun i (hi:i∈P)=> (integral_indicator (f:=V) (h i hi)).symm), ← integral_finsetSum]; swap; exact fun i hi => hW.indicator (h i hi)
    refine integral_mono (hW.indicator hm) (integrable_finsetSum P fun i hi=> hW.indicator (h i hi)) (fun i=> ?_)
    have hx q : 0 ≤ (t q).indicator V i := Set.indicator_nonneg (fun _ _=> hV _) _
    by_cases hi:i∈W
    · rw [Set.indicator_of_mem hi]; obtain ⟨j,hj,hk⟩:= he i hi; exact ((Set.indicator_of_mem hk V).symm.le.trans (single_le_sum (f:= fun j=> (t j).indicator V i) (fun j _=> hx _) hj))
    rw [Set.indicator_of_notMem hi]; exact sum_nonneg fun i _=>hx i

variable (X)
def breach (j:ι) (s:ℝ): Set (Sky G ι):= {x| (fare s)^2 ≤ nib x j}
lemma breach_borel (j:ι)(s : ℝ):MeasurableSet (breach (G:=G) j s):=by unfold breach nib; exact isClosed_le continuous_const (by fun_prop) |>.measurableSet
lemma wallet (G:Gauge) : ∀ᶠ s:ℝ in atTop, ∀ (n:Side)(ι k T:Type) (_:Fintype ι) (_:Fintype k) (_:Fintype T)
    (B:Base G n ι k T) (_H:B.Admits X (dollar s))(R:ℕ), R≤ stride X (rungs X s) → ∀ z,
      (∫ x in riot B.loc z X ((fare s)^2) R, B.output (dollar s) x ∂skillet G ι) ≤ riotFee s*∫ x,B.output (dollar s) x ∂skillet G ι:=by
    filter_upwards [cost_late X G,eventually_gt_atTop (0:ℝ)] with s hs he n ι k T _ _ _ B H R hR z
    let a:= neighborsOf B.loc R z; let g:=dollar s; have hg:0<dollar s:= dollar_pos _
    have hgt:0<g/4:=by unfold g; positivity
    let b:=(g/4) ^ burn G
    let F:=B.output g; let Z:=∫ x,F x∂skillet G ι; let L:=s+Real.log 4; let w:=weights X (stride X (rungs X s)); let k:= rider X*weights X (R+X.b) - (fare s)^2/(2*dam X*g^2)
    have hL:0<L:=add_pos he (Real.log_pos (by norm_num))
    apply le_of_mul_le_mul_left (a:=b^a.card) ?_ (pow_pos (pow_pos hgt _) _)
    have h:= Base.riot_cost H (R:=R) (z:=z) ((fare s)^2) hg (dollar_bound he.le)
    refine h.trans ?_; change Real.exp k* Z ≤ _ ; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (show 0≤Z from integral_nonneg (fun i=> Base.output_pos H i|>.le))
    have hx : -L=Real.log (g/4):=by unfold L g; rw [Real.log_div hg.ne' (by norm_num),dollar,Real.log_exp]; ring
    have hb:=show b^ a.card = Real.exp (-(a.card:ℝ)*(burn G:ℝ)*L) from by
       unfold b; rw [← Real.exp_log hgt,← hx, ←Real.exp_nat_mul,←Real.exp_nat_mul]; congr 1; ring
    rw [hb,riotFee,←Real.exp_add, Real.exp_le_exp]; have hd:=@rider_pos X
    have hv : (a.card:ℝ) ≤ w:= (Nat.cast_le.mpr (price_cover H.core ..)).trans (weights_mono X hR)
    have hm:= mul_le_mul_of_nonneg_left hv (show 0 ≤ L * (burn G:ℝ) from by positivity)
    change _-_/(2* dam X*g^2) + L*(burn G:ℝ)*w ≤ _ at hs
    unfold k; nlinarith only [hs,mul_le_mul_of_nonneg_left (weights_mono X (Nat.add_le_add_right hR X.b)) hd.le,hm]

lemma shield (G:Gauge) : ∀ᶠ s:ℝ in atTop, ∀ (n:Side)(ι k T:Type) (_:Fintype ι) (_:Fintype k) (_:Fintype T)
    (B:Base G n ι k T) (_H:B.Admits X (dollar s)) (i:ι),
    (∫ x in breach i s,B.output (dollar s) x ∂skillet G ι) ≤ ruin s*∫ x,B.output (dollar s) x ∂skillet G ι:=by
   filter_upwards [wallet X G,last X,ruin_rings X] with s hs he hh n ι k T _ _ _ B H i
   let W:= B.output (dollar s); let Z:= ∫ x,W x ∂skillet G ι; have hp x:0≤W x:= Base.output_pos H x|>.le
   let r:=(fare s)^2; let u:=rungs X s; let z:= B.loc i
   let t (m:ℕ):=riot (G:=G) B.loc z X r (stride X m)
   refine (union_cost (range u) t (fun _ _=> measurableR ..) _ ((Base.output_env H).integrable _) hp _ (breach_borel ..) (fun x hx=> calm B.loc H.core x i r hx u he)).trans ((sum_le_sum (g:=fun _=>riotFee s* Z) (fun i hi=>hs n ι k T _ _ _ B H _ (by unfold stride; gcongr; exact (mem_range.mp hi).le) z)).trans ?_)
   rw [sum_const,nsmul_eq_mul,card_range,←mul_assoc]; exact mul_le_mul_of_nonneg_right hh (integral_nonneg hp)
end YM.RGComparison.Core16.Forge
