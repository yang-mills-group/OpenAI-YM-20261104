import YM.MS.Symbol
import YM.MS.LogTime

/-!
# Agreement of Taylor jets at large heat length implies the symbol comparison

This is the high-scale integration argument in Prop add-high of the addendum.
We give versions admitting other uniform parameters (period, log subtraction
scale, positions when applied to joined terms). Intersect later for IR intervals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.LogTime
open Real Function Filter Set
open scoped Topology ContDiff Interval
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

variable (S : Scale ι)
variable [NormedSpace ℝ E] [NormedSpace ℝ F]
-- descend jets, with mean-value integration on balls
variable {f : Kern ι E F} {g : ι → ℝ} {j : ℕ}
lemma lower_jet (h : ∀ i, ContDiff ℝ ∞ (f i))
    (hz : S.full.Le (fun i (_p:E) => ‖iteratedFDeriv ℝ j (f i) 0‖) (fun i _ => g i*S.length i^j))
    (hp : S.full.Part S f (fun i _ => g i) (j+1)) :
    S.full.Part S f (fun i _ => g i) j := by
  let W (i : ι) (p : E) := S.basic i * S.weight i p
  have hW (i : ι) (p : E) : 1 ≤ W i p := S.full.one_le i p (mem_univ _)
  have hg : ∀ i, 0≤ g i := fun i=> Cost.Part.nonneg _ hp i 0 (mem_univ _)
  have ht i : 0≤ g i*S.length i^j:= mul_nonneg (hg i) (pow_nonneg (S.pos i).le _)
  let F i (x : E) := iteratedFDeriv ℝ j (f i) x
  -- first estimate subtraction
  have he : S.full.Le (fun i p=> ‖F i p-F i 0‖) fun i _=> g i*S.length i^j := by
    obtain ⟨C,hC,b,H⟩ := hp
    refine ⟨C,hC,b+1,fun i p _=>?_⟩
    let K:= C* W i p ^ b*(g i*S.length i^(j+1))
    have hl:=S.pos i; have h0:= ht i; have hg:=hg i
    have hI : ∀ q ∈ Metric.closedBall (0:E) ‖p‖, ‖fderiv ℝ (F i) q‖ ≤ K := by
       intro q hq; rw [show F i = iteratedFDeriv ℝ j (f i) from rfl,norm_fderiv_iteratedFDeriv]
       have hq' : ‖q‖ ≤ ‖p‖:= by simpa using hq
       have he := S.basic_pos i; have hw := hW i q
       have hw' : W i q ≤ W i p:= by dsimp only [W,Scale.weight]; gcongr
       apply (H i q (mem_univ _)).trans; change C* W i q ^ b * _ ≤ _; unfold K; gcongr
    have hm := (convex_closedBall 0 ‖p‖).norm_image_sub_le_of_norm_fderiv_le (f:=F i) (𝕜:=ℝ) (fun x _=> (h i).differentiable_iteratedFDeriv (m:=j) (by norm_cast; exact WithTop.coe_lt_top j) x) hI (x:=0) (by simp) (y:=p) (by simp)
    simp only [sub_zero] at hm; apply hm.trans
    have hw : S.length i*‖p‖ ≤ W i p := by
      trans S.weight i p
      · unfold Scale.weight; linarith
      exact le_mul_of_one_le_left (S.weight_pos i p).le (S.one_le i)
    change K* _ ≤ C* W i p ^ _ * _
    obtain hv:=hW i p; calc
      _ = C* W i p ^ b * (g i*S.length i^j)*(S.length i*‖p‖) := by unfold K; ring
      _ ≤ C* W i p ^ b * (g i*S.length i^j)*W i p := by apply mul_le_mul_of_nonneg_left hw; positivity
      _ = _ := by dsimp; ring -- dsimp check
  refine (he.add hz (fun i _ _ => ht i)).left fun i p _=>?_
  exact le_of_eq_of_le (congr_arg norm (sub_add_cancel (F i p) (F i 0)).symm) (norm_add_le ..)

end YM.MS.LogTime
