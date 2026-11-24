import YM.QuadraticLocal.Tint.Unit
/-!
 # Total teacher-turn budgets over ALL Jobs at the one Θ. Includes support masks.
 Need complete kernel Exponential and Full Budget on shape anyway, but this is revenue
 beyond reading and can consume stencil-by-stencil education.Body_C. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tint.Campus.Hearth.Week
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder AllOrder.Ink
open Push.SectorMeasure ConnectedActivityE6 RemainderComparison Trigger Patrol
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι J: Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e r b k τ L v' :ℝ} {s i' j h m : ℕ}
variable (X:ι→Row P R G α) (C:Club X)
open Travel Club Typeface Lyric
variable {U:RG.Rep G n} (T:Incoming P U α J R)
variable (w:V→ℝ)(hw:∀ i,0<w i) (B:BudgetPoint)[Countable ι] (S:StepData c n)(H R₀:ℕ)(ψ:ℝ)
set_option quotPrecheck false
local notation "K"=> Job X H S U
local notation "Φ" i:max=> Accumulate.rootPrice X w τ i
variable (hp:Offers X w τ b)(he:b≤1)(hL:∀ i:Club X,i.val.card ≤ m)(ha:0≤a)(hA:0≤τ)
local notation "C₁" x:max=> (Club.roof X x S.ratio)
local notation "L'"=> S.ratio.count

def maxFee (N: Side)(m H R₀:ℕ)(θ v:ℝ):ℝ:= 2*(ballCost R₀:ℝ)*(2:ℝ)^m * Breeze.areaBudget H m ((N.val:ℝ)^4)*Real.exp (θ*v)
local notation "b₀"=> Breeze.areaBudget H m ((S.ratio.count.val:ℝ)^4)
omit [Countable ι] in
lemma maxFee_pos (N: Side)(m H R₀:ℕ)(θ v:ℝ):0 < maxFee N m H R₀ θ v:=by unfold maxFee Breeze.areaBudget Animals.ballCost; positivity
include hw hp he hL hA S U
lemma budget (x:Site c): SumBudget (fun i:Job X H S U=>if C₁ i.val.1=x then Week.pack X i.val.1 w else 0) (2^m*(b*b₀)):=by
   let f(i:Campus.Batch X):= if Accumulate.closer X S.ratio i.fst x H then pack X i.fst w else 0; let u(i:Club X):= if Accumulate.closer X S.ratio i x H then Φ i else 0; let D(i:Club X):=(2:ℝ)^m*u i; have hD : SumBudget D (2^m*(b*b₀)):= budget_scale (by positivity) (Accumulate.inside m X S.ratio w hw hp he hL H x)
   have ht: SumBudget f (2^m*(b*b₀)):=by
       apply Width.trapeze f hD; intro i; by_cases hh:Accumulate.closer X S.ratio i x H; swap; · apply budget_finite; intro j; unfold f; rw [if_neg hh]; unfold f; dsimp only; simp_rw [if_neg hh,Finset.sum_const_zero]; exact hD.1 _
       apply budget_finite; intro j; unfold f; dsimp only; rw [if_pos hh]; exact (Week.strict X i w hw).le
       unfold f D u; dsimp only; simp_rw [if_pos hh,sum_const,nsmul_eq_mul]; have he:(Fintype.card (Patrol.Signs X i):ℝ)≤ (2:ℝ)^m:= by unfold Patrol.Signs; rw [Fintype.card_pi]; simp only [Fintype.card_bool,Finset.prod_const,Finset.card_univ]; rw [Fintype.card_fin]; exact_mod_cast pow_le_pow_right₀ (show (1:ℕ)≤2 by decide) (hL i)
       exact mul_le_mul he (Week.economize X i w hw τ hA) (Week.strict X i w hw).le (by positivity)
   convert budget_pull Subtype.val Subtype.val_injective ht using 1; ext i; unfold f; by_cases hX:C₁ i.val.1=x; rw [if_pos hX,if_pos (show Accumulate.closer X S.ratio i.val.fst x H from ⟨i.prop.1,hX⟩)]; rw [if_neg hX,if_neg (show ¬ Accumulate.closer X S.ratio i.val.fst x H from fun h=> hX h.2)]
include ha
lemma charge (hv:0≤v')(hQ:∀ i:Job X H S U,( Lattice.coverNumber B.B (neighbors R₀ (Club.roof X i.val.fst S.ratio)):ℝ)≤ ψ): Hit (fun i:Job X H S U=>neighbors R₀ (C₁ i.val.fst)) B.B (fun i=>2*(v'*pack X i.val.fst w)) a (maxFee S.ratio.count m H R₀ a ψ *b*v'):= by
    intro x; let S₁:= neighbors R₀ x; let V:= Real.exp (a*ψ); let f i (j:K):= if C₁ j.val.fst=i then 2*v'*V*pack X j.val.fst w else 0; have hF(i):SumBudget (f i) ((2*v'*V)*(2^m*(b*b₀))):= by
        convert budget_scale (x:=2*v'*V) (by unfold V; positivity) (budget (U:=U) X w hw S H hp he hL hA i) using 1; ext j; unfold f; split; rfl; rw [mul_zero]
    have hQ':= budget_over S₁ _ _ (fun i _=>hF i); refine budget_loosen (budget_mono hQ' ?_ (fun i=>?_)) ?_
    · intro i; split; next=> have he:= Week.strict X i.val.1 w hw; dsimp only; positivity
      next=> exact le_refl _
    · split; next hh=>
         change x∈ neighbors R₀ (C₁ i.val.fst) at hh; let y:= C₁ i.val.fst; have he':y∈ S₁:= (neighbors_mem ..).2 ((separation_comm ..).trans_le ((neighbors_mem ..).1 hh)); refine le_trans (b:=f y i) ?_ (Finset.single_le_sum (f:=fun j=>f j i) (fun j _=> (hF j).1 _) he'); unfold f; rw [if_pos (show _=y from rfl)]; have hV:= Week.strict X i.val.1 w hw; apply (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (hQ i) ha)) (by positivity : 0≤2*(v'*pack X i.val.1 w))).trans; unfold V; apply le_of_eq; ring
      next=> exact hQ'.1 _
    unfold maxFee; rw [sum_const,nsmul_eq_mul]; have hh:=budget_nonneg (hF x); apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (neighbors_card R₀ x)) hh).trans; apply le_of_eq; unfold V; ring
end YM.QuadraticLocal.Tint.Campus.Hearth.Week
