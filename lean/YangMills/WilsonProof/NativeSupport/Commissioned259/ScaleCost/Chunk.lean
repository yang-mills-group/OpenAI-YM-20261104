import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Metrics
import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Out
/-!
# Complete also (G.1) compact ratio version, including arbitrary fixed upper ratio

Derive on entire continuum intervals from our theorem `movement`, by taking any std. growth
budget then lowering perturbative comparison order on these smaller ratio windows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Function Set Asymptotics Comparing Matrix PowerSeries
open MS.Book.Program XSpace XSpace.Normalize O.Score O.Enh Dframe FVA2.Scale Quotes
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ} {B : ℝ→Frames G} (H : Law V R B)
variable {W W' : ℝ} {I : Type*} {X : Filter I} {η T r : I→ℝ} {S : Set ℝ}
local notation "late" =>𝓝[>] (0:ℝ)
local notation "home" => fun (_:I)=>(1:ℝ)

private lemma compact_income {S:Set ℝ} {f:ℝ→ℂ} (hc:IsCompact S) (hx:Continuous f) (h:∀ᶠ i in X, η i∈S) : Fare home X home (f∘η) := by
  obtain ⟨C,H⟩:=hc.exists_bound_of_continuousOn hx.continuousOn
  exact Fare.cent (h.mono fun i hi=>H _ hi)
private lemma compact_purse {S:Set ℝ} {f:ℝ→ℂ} (hc:IsCompact S) (hf:Rhythm f) (h:∀ᶠ i in X, η i∈S) : Fare home X home (f∘η) := by
  obtain ⟨p,rfl⟩:= Rhythm.from_poly.mp hf
  exact compact_income hc (by fun_prop) h
include H
lemma ψ_compact (hc:IsCompact S)(h:∀ᶠ i in X, η i∈S) : Tunes home X home (fun i=>R (η i)) :=
  fun n=> compact_purse hc ( Rhythm.unit.mpr ( H.smooth n ) ) h
lemma poles_compact (d : ℕ) (hc:IsCompact S)(h:∀ᶠ i in X, η i∈S) : Quotes.Uniform home X home (fun i=>conversion B (η i) d) := by
  let Q i:= C (Level.Dial (G:=G) d (η i)); let L' i:=B (η i) d
  have hey : Quotes.Uniform home X home L' := fun a b p=> by
    simp_rw [prose,coeff_mk]; exact compact_purse hc (H.proper d p (theory b) (coord a)) h
  have y : Quotes.Uniform home X home Q := by
    intro i j p; simp_rw [Q,prose,coeff_mk,coeff_C]; by_cases hp:p=0
    · simp_rw [if_pos hp]; refine compact_income (f:=fun t=>engine G d t i j) hc ?_ h; simp_rw [gear_cost]
      by_cases hy:j=i <;> simp [hy] <;> fun_prop
    simp_rw [if_neg hp]; exact Fare.constant _
  intro i j k; exact (Quotes.Uniform.product (Eventually.of_forall fun _=>le_refl _) y hey i j k).extend (Eventually.of_forall fun _=>one_mul _)
omit H
variable (hG : G.Simple) {t : ℝ→ℝ} (ht : t=O[late] (g0 G)) {D : Route G} (hD : Balances D) (P : StepCost G R B t D)
    (hr : Tendsto r X late) (hT : ∀ᶠ i in X,T i ∈ Icc 1 W)
    {d : ℕ}
local notation "g" => g0 G ∘ r
local notation "s" => (fun i:I=>r i*T i)
local notation "α" => t∘r
local notation "Qη" => fun i:I=> -Real.log (T i)
include hG hr hT
lemma upper_uniform : Tendsto s X late ∧ (g0 G ∘ r)=O[X] (g0 G ∘ s) ∧ (g0 G ∘ s)=O[X] (g0 G ∘ r) := by
  have e: ∀ᶠ i in X, permit G W 0 (r i) (s i) 1 := by
    filter_upwards [hr.eventually self_mem_nhdsWithin,hT] with i hr ht
    have e : 0 < r i := hr
    exact ⟨le_mul_of_one_le_right e.le ht.1,le_rfl,(by rw [neg_zero,Real.rpow_zero,mul_one,mul_one]; exact mul_le_mul_of_nonneg_left ht.2 e.le)⟩
  obtain ⟨h,u,p⟩:= corridor hG hr e; exact ⟨h,p,u⟩
lemma into_budget : ∀ᶠ i in X,1 ≤ T i ∧ T i ≤ 1*(g0 G (r i))^(-(1:ℝ)) := by
  filter_upwards [hT, hr.eventually (Comparing.ample hG 1 zero_lt_one W 1 zero_lt_one)] with i ⟨v,h⟩ e
  exact ⟨v,h.trans e⟩
include H ht hD P
lemma long_chunk (d k : ℕ) : ∀ᶠ p:ℕ in atTop,
    (fun i=> stiffness (actual D d (r i) (T i)-form B d (T i) p (α i)))=O[X] (fun i=> g0 G (r i)^k) ∧
    (fun i=> (↑(t (s i)):ℂ)-crop p (α i) (R (Qη i)))=O[X] (fun i=> g0 G (r i)^k) := by
  filter_upwards [movement (a:=1) H hG ht (show 0<(1:ℝ) from zero_lt_one) k hD P d] with p ⟨M,hM,h⟩
  have z := now ((pace hG).comp hr) |>.and ((into_budget hG hr hT).and (hr.eventually h))
  constructor
  · refine IsBigO.of_bound M (z.mono fun i ⟨u,⟨x,v⟩,h⟩=>?_)
    rw [Real.norm_of_nonneg (stiffPos _), Real.norm_of_nonneg (pow_nonneg (show 0 ≤ g0 G (r i) from u.le) _)]
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (h _ x v)
  refine IsBigO.of_bound M (z.mono fun i ⟨u,⟨x,v⟩,h⟩=>?_)
  rw [Real.norm_of_nonneg (pow_nonneg (show 0 ≤ g0 G (r i) from u.le) _)]
  exact (le_add_of_nonneg_right (stiffPos _)).trans (h _ x v)
lemma chunk (p d : ℕ) : (Notes X home α g p home (fun i=> D (r i) (s i) d) (fun i=>conversion B (Qη i) d)) ∧
    Coin X home α g p home (fun i=>(↑(t (s i)):ℂ)) (fun i=>R (Qη i)) := by
  obtain ⟨j,hj,M₀,K⟩:= ((eventually_ge_atTop p).and (long_chunk H hG ht hD P hr hT d (p+1))).exists
  have φ : ∀ᶠ i in X,Qη i ∈ Icc (-Real.log W) 0 := hT.mono (fun i ⟨l,r⟩=>⟨neg_le_neg (Real.log_le_log (by linarith) r), neg_nonpos.mpr (Real.log_nonneg l)⟩)
  have ha:∀ᶠ i in X,|α i| ≤ 1:= ((ht.trans_tendsto (g0_zero hG)).comp hr |>.abs).eventually (ge_mem_nhds (by norm_num))
  have hc {u:I→ℂ}{f:I→PowerSeries ℂ}(hi:Tunes home X home f)(he:(fun i=>u i-crop j (α i) (f i))=O[X] (fun i=>g i^(p+1))) : Coin X home α g p home u f :=
    ⟨hi,(Fare.add (Eventually.of_forall fun _=> le_refl _) ((Fare.bare he).extend (Eventually.of_forall fun i=>(mul_one _).symm)) (Tunes.excess (Eventually.of_forall fun _=> le_refl _) ha (ht.comp_tendsto hr) j p hj hi)).congr (Eventually.of_forall fun i=>sub_add_sub_cancel ..) ⟩
  exact ⟨fun i j=>hc (poles_compact H _ isCompact_Icc φ i j) (matrixPay.mp M₀ i j), hc (ψ_compact H isCompact_Icc φ) K⟩
end YM.FVA2.GradedFar259.ScaleCost
