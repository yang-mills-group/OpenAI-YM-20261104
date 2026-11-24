import YangMills.WilsonProof.NativeSupport.Commissioned259.Sparks.Invert
/-! # Precision along the *true* late filter (having actual points) pins its coefficients -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Sparks
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix Quotes
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I J: Type*} {L: Filter I}{F:Filter J} {t g w:I→ℝ} {V:I→PowerSeries ℂ}
lemma Worth.unique [L.NeBot] {q p:PowerSeries ℂ}{f:I→ℂ} (h:Worth L t g f q)(v:Worth L t g f p)
    (hc:g=O[L] t) (ht : Tendsto t L (𝓝[>] 0)) : q=p := by
  refine PowerSeries.ext fun i=>?_ ; induction i using Nat.strong_induction_on with| h i ih=>
     let a:= coeff i p-coeff i q; have hh : (fun k => crop i (t k) p-crop i (t k) q)=O[L] fun k=>t k^(i+1) := by
        refine (((homebound (h i).expense).sub (homebound (v i).expense)).trans ((hc.pow (i+1)).congr_left (fun i=> (mul_one _).symm))).congr_left fun i=>?_
        abel
     have eq k : crop i (t k) p-crop i (t k) q=(t k:ℂ)^i*a := by
        simp_rw [crop_apply, Finset.sum_range_succ]; have hx : ∑j∈Finset.range i,(t k:ℂ)^j*coeff j p=∑j∈Finset.range i,(t k:ℂ)^j*coeff j q:= Finset.sum_congr rfl fun j hj=>by rw [ih _ (Finset.mem_range.mp hj)];
        rw [hx]; unfold a; ring
     obtain ⟨c,hc,H⟩:=hh.exists_pos; suffices H : ‖a‖=0 from Eq.symm (sub_eq_zero.mp (norm_eq_zero.mp H));
     have e : Tendsto (fun i=> c*t i) L (𝓝 0) := by simpa only [mul_zero] using ((ht.mono_right nhdsWithin_le_nhds).const_mul c)
     refine le_antisymm ( ge_of_tendsto e ?_ ) (norm_nonneg _); filter_upwards [H.bound,ht.eventually self_mem_nhdsWithin] with k h hi
     replace hi : 0<t k := hi; rw [eq k, norm_mul,norm_pow,Complex.norm_real, norm_pow, Real.norm_of_nonneg hi.le,pow_succ, mul_left_comm c ] at h; exact le_of_mul_le_mul_left h (pow_pos hi i)
variable {G:Gauge} (hG:G.Simple) {t':ℝ→ℝ} (paid: Calibrated G t')
local notation "late" => 𝓝[>] (0:ℝ)
include hG paid
lemma clock_scale : g0 G=O[late] t' := by
  apply IsBigO.of_bound 2
  filter_upwards [g0_pos hG, coupling_payment hG paid, ( show Tendsto _ _ _ from paid ).eventually_const_lt (show (1:ℝ)/2<1 by norm_num)] with i h e f; rw [Real.norm_of_nonneg h.le,Real.norm_of_nonneg e.1.le]; replace f:= (lt_div_iff₀ h).mp f; linarith
omit hG paid

lemma narrow (A:I→ℂ)(p:ℕ){f:J→I}(h:Tendsto f F L)(ht: Coin L Pose.home t g p Pose.home A V) :
    Coin F Pose.home (t∘f) (g∘f) p Pose.home (A∘f) (V∘f) := by
   refine ⟨ fun i=>Fare.bare ((homebound (ht.prices i)).comp_tendsto h), Fare.bare ((homebound ht.expense).comp_tendsto h) ⟩

-- ready for PT applications even if L=bottom. This direction doesn't need NeBot.
lemma Worth.comp {X:I→ℂ} {A:PowerSeries ℂ} {f:J→I} (hz : Tendsto f F L)(ht: Worth L t g X A) :
    Worth F (t∘f) (g∘f) (X∘f) A := fun p=>narrow X p hz (ht p)
end YM.FVA2.GradedFar259.Sparks
