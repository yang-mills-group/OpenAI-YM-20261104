import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Voyage
import YM.Push.STATIONARY_UNIFORM.Entries
/-! # The real analytic curvature germs needed for all grade stencils

Compact, at ALL station positions (including off station, on any
auxiliary tori). Need uniform un-divided derivative receipts even if a
real tag moves the saddle farther than an available station-before phase. Split the exponential exactly BEFORE estimating it, not Taylor expanding on
a large ball.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Sounder
open AnalyticNext.QuarticMatch.Estimate Push.Uniform Gauge Logfee
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
open NormedSpace Finset
variable {G : Gauge}
variable {E ι:Type}[DecidableEq ι][NormedAddCommGroup E][NormedSpace ℝ E]
variable (S:Finset ι)(d:ι→E)
/-! Power method: derivative terms with all labelled slots assigned to
exp(z/m)^m. A unitary factor when no slot is assigned costs zero
multiplicative loss. Eg crude product of opNorm bounds incl slot-zero
(to m-th power) would NOT cancel with scaling and doesn't work. -/
lemma in_series (l:E→G.El) (x:E)(n m:ℕ) (h:S.card ≤ m)(hf:ContDiffAt ℝ ω (fun x=>G.mat (l x)) x){T:ℝ}(ht:0≤T)(u:ι→ℝ)(hu:∀i∈S,0≤u i) (he:∀ t∈S.powerset, t.Nonempty → ‖bill t d (fun x=>G.mat (l x)) x‖ ≤ T^t.card* ∏ i∈t,u i) :
    ‖bill S d (fun x=>G.mat (l x)^n) x‖ ≤ ample G*(T^S.card*∏ i∈S,(n*u i)):=by
  let φ:= ContinuousLinearMap.mul ℝ G.Mat
  induction n generalizing S with
  | zero=>
    simp_rw [pow_zero]
    rcases S.eq_empty_or_nonempty with he|he
    · subst S; simp [blank,ample]
    rw [mute he, norm_zero]; exact mul_nonneg (ample_pos _).le (mul_nonneg (by positivity) (prod_nonneg (fun _ _=> by simp)))
  | succ n hi=>
    let f y:= G.mat (l y); let g y:= f y^n
    have hg: ContDiffAt ℝ ω g x:=hf.pow _
    change ‖bill S _ _ _‖ ≤ _; simp_rw [pow_succ']
    rw [show (fun a:E => G.mat (l a)*G.mat (l a)^n) = fun x=>φ (f x) (g x) from rfl, account φ S d f g x hf hg]
    simp_rw [Nat.cast_add_one,add_comm (_:ℝ) 1,add_mul,one_mul]; rw [prod_add,mul_sum,mul_sum]; apply (norm_sum_le ..).trans; refine sum_le_sum fun t hh=>?_ ; replace hh := mem_powerset.mp hh
    have hc : (S\t).card ≤ m := (card_le_card sdiff_subset).trans h
    have hG:=hi (S:=S\t) hc (fun i hi=>hu i (sdiff_subset hi)) (fun i ih=> he i (mem_powerset.mpr (Subset.trans (mem_powerset.mp ih) sdiff_subset)))
    rcases t.eq_empty_or_nonempty with h1|h1
    · subst t; change ‖f x * bill (S\∅) d g x‖ ≤ _ -- defeq bill0?
      simpa only [confirms, sdiff_empty, prod_empty,one_mul, f] using! hG -- target confirms may missing change
    have hF:= he _ (mem_powerset.mpr hh) h1
    apply ((norm_mul_le ..).trans (mul_le_mul hF hG (norm_nonneg _) ((norm_nonneg _).trans hF))).trans_eq
    have hy:T^t.card*T^(S\t).card=T^S.card:=by rw [←pow_add,Nat.add_comm t.card, Finset.card_sdiff_add_card_eq_card hh]
    rw [← hy]; ring

lemma endless {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X](L:X →L[ℝ] G.Color)(x:X) (n k:ℕ)(hk:k ≤ n) :
    ‖iteratedFDeriv ℝ k ((fun a : G.Color=>G.mat (G.lieExp a)) ∘ L) x‖ ≤ ample G * ((unitPrice G n).C * ‖L‖)^k :=by
  let F:=(fun a : G.Color=>G.mat (G.lieExp a))
  let C:= (unitPrice G n).C
  have hC: 1≤C:= (unitPrice G n).used
  have ha:= ample_back G
  obtain ⟨b,hm⟩ := exists_nat_gt ‖L x‖
  have hb':(0:ℝ)<b:=(norm_nonneg _).trans_lt hm
  let M:= (b:ℝ)⁻¹ • L
  let s y:=G.lieExp (M y)
  have he: F ∘ L = fun y=>G.mat (s y)^b:=by
    funext y
    simp only [Function.comp_apply,F,s, mat_lieExp,M,smul_apply, map_smul]
    letI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
    have hz : exp (b • ((b:ℝ)⁻¹ • G.colorMat (L y)))=exp ((b:ℝ)⁻¹ • G.colorMat (L y))^b:=exp_nsmul b _
    rw [← hz, ← Nat.cast_smul_eq_nsmul ℝ,smul_smul,mul_inv_cancel₀ hb'.ne',one_smul]
  have hf:ContDiff ℝ ω F:=G.exp_jet
  have hh:ContDiffAt ℝ ω (fun x=>G.mat (s x)) x:=(hf.comp M.contDiff).contDiffAt
  have h2: ‖M x‖≤1:=by
    change ‖(b:ℝ)⁻¹ • (L x)‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; rw [inv_mul_le_iff₀ hb',mul_one]; exact hm.le -- hm.le
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun d=>?_
  rw [← univEstimate d _ _ (hf.comp L.contDiff).contDiffAt,he]
  let P₀:= C*((b:ℝ)⁻¹*‖L‖)
  have hp:0≤ P₀:=by unfold P₀; positivity
  have hu:= in_series (G:=G) (Finset.univ:Finset (Fin k)) d s x b n (by simpa using hk) hh hp (fun i=>‖d i‖) (by intros; positivity) (by
    intro t ht ht'
    let D i:= M (d i)
    change ‖bill t d (F ∘ ⇑M) x‖ ≤ _
    rw [readdress t d M x hf]
    have hbb : ∏ i∈t,‖D i‖ ≤ ∏ i∈t,((b:ℝ)⁻¹*‖L‖)*‖d i‖:= by
      refine prod_le_prod (fun _ _=>norm_nonneg _) fun i _=> ?_
      change ‖(b:ℝ)⁻¹ • L (d i)‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg (by positivity),mul_assoc]; exact mul_le_mul_of_nonneg_left (L.le_opNorm _) (by positivity)
    have hc : t.card ≤ n := (card_le_univ _).trans (by simpa using hk)
    refine (bill_bound ..).trans ?_
    change _*(∏ i∈t,‖D i‖)≤ _
    refine (mul_le_mul ((unitPrice G n).he _ hc (card_ne_zero.mpr ht') _ h2) hbb (prod_nonneg fun _ _=>norm_nonneg _) (show 0≤C^_ by positivity)).trans_eq ?_
    rw [prod_mul_distrib,prod_const,show (unitPrice G n).C=C from rfl]; unfold P₀; ring)
  apply hu.trans_eq
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hy : P₀*b=C*‖L‖:=by unfold P₀; field_simp
  rw [← hy,mul_pow]; ring

noncomputable def eUniversal (G:Gauge)(n:ℕ):ℝ:= ample G*(1+(unitPrice G n).C)^n
lemma genuine (G:Gauge)(n:ℕ)(x:G.Color):Allows n (fun a : G.Color=>G.mat (G.lieExp a)) x (eUniversal G n):=by
  have h:= (unitPrice G n).used
  have h':=ample_back G
  refine ⟨G.exp_jet.contDiffAt,?_⟩; intro k hk
  refine (endless (ContinuousLinearMap.id ℝ G.Color) x n k hk).trans ?_
  unfold eUniversal; gcongr
  refine (pow_le_pow_left₀ (by positivity) (show (unitPrice G n).C*‖ContinuousLinearMap.id ℝ G.Color‖ ≤ 1+(unitPrice G n).C from (mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le).trans (le_add_of_nonneg_left (by positivity))) _).trans (pow_le_pow_right₀ (by linarith) hk)
end YM.RG01.Sounder
