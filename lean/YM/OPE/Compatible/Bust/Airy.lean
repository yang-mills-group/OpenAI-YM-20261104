import YM.OPE.Compatible.Begun.Mask
import Mathlib.Analysis.Normed.Lp.lpSpace
/-! # Banach rank actual -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module
open scoped Topology BigOperators Classical
variable {I K E:Type}{m r i j n k:ℕ}{C:ℝ}
abbrev stave (_ r:ℕ)(I:Type):= lp (fun _:Page I r=>ℝ) 1
-- m param weighting
noncomputable def seed (m r:ℕ)(I:Type): stave m r I→ₗ[ℝ] Script I r where
    toFun f i:= f i /figure m i
    map_add' a b:=by funext i; change (a i+b i)/_= _; rw [add_div];rfl
    map_smul' a b:=by funext i; change (a*b i)/_ =a*(b i/_);ring
def plant (m:ℕ)(p:Script I r)(C:ℝ)(h:soot m p C):stave m r I:=⟨fun i=> p i*figure m i, memℓp_gen (by
    let f(i):= p i*figure m i; have hp(i): ‖f i‖=figure m i* ‖p i‖:=by unfold f; rw [norm_mul,Real.norm_of_nonneg (zero_le_one.trans (payer m i)), mul_comm]
    change Summable fun i=> ‖f i‖^ ENNReal.toReal (1: ENNReal); simpa only [ENNReal.toReal_one,Real.rpow_one,hp] using h.2.1)⟩
lemma figure_pos (i:Page I r):0<figure m i:= lt_of_lt_of_le zero_lt_one (payer _ _)
lemma botany (m:ℕ)(p:Script I r)(C:ℝ)(h:soot m p C): seed m _ _ (plant m p C h) = p:= by funext i; exact mul_div_cancel_right₀ _ (figure_pos _).ne'
lemma sprig (m r:ℕ)(x:stave m r I): HasSum (fun i=> figure m i*‖seed m r I x i‖) ‖x‖:=by
     have hp(i:Page _ r): figure m i *‖seed m r I x i‖=‖x i‖:=by change _*‖x i/figure m i‖=_; rw [norm_div, Real.norm_of_nonneg (show 0 ≤ figure m i from (figure_pos _).le)]; have ht:0 < figure m i:=figure_pos _; field_simp
     simp_rw [hp]; simpa only [ENNReal.toReal_one,Real.rpow_one] using lp.hasSum_norm (show 0 < ENNReal.toReal (1: ENNReal) from by simp) x
lemma humor (x:stave m r I): soot m (seed m r I x) ‖x‖:=⟨fun i=>mul_nonneg (figure_pos i).le (norm_nonneg _),(sprig _ _ _).summable,(sprig _ _ _).tsum_eq.le⟩
lemma kept_stalk {p:Script I r} (h:soot m p C):‖plant m p C h‖≤C:= by rw [← (sprig m r (plant m p C h)).tsum_eq,botany m _ _ h]; exact h.2.2
lemma seed_inj (m r:ℕ)(I:Type): Injective (seed m r I):=fun x y h=>lp.ext (p:=1) (funext fun i: Page I r=>by apply mul_right_cancel₀ (inv_ne_zero (figure_pos i).ne'); exact show x i*(figure m i)⁻¹=y i*(figure m i)⁻¹ from (show _ from congr_fun h i)) -- div not def
-- hut Fintype bundled
abbrev Seat (k m:ℕ)(I:Type):= (j: Fin (k+1))→ stave m j.val I
lemma stonesNorm (v:stave m r I)(i:Page I r): ‖seed m r I v i‖ ≤ ‖v‖:= (le_mul_of_one_le_left (norm_nonneg _) (payer m i)).trans (Sack.single (humor (m:=m) v) i)
def stairL (m:ℕ)(i:Page I r): stave m r I→L[ℝ] ℝ:= (LinearMap.proj (R:=ℝ) i ∘ₗ seed m r I).mkContinuous 1 (fun v=> (stonesNorm (m:=m) v i).trans_eq (one_mul _).symm)
noncomputable def down (I:Type)(r m:ℕ)(k:ℕ)(h:k≤m):stave m r I →L[ℝ] stave k r I:= LinearMap.mkContinuous {
       toFun p:= plant k (seed m r I p) ‖p‖ (Cascade.Rill.soot_le_k (seed m r I p) _ (humor p) h)
       map_add' a b:=seed_inj k r _ (by simp only [map_add,botany])
       map_smul' a b:=seed_inj k r _ (by simp only [map_smul,botany];rfl) }
       1 (fun p=> le_trans (kept_stalk (Cascade.Rill.soot_le_k (seed m r I p) _ (humor p) h)) (one_mul _).symm.le)
