import YM.Pert.Triangle.Epsilon
import YM.Pert.Triangle.OuterShift
import YM.Pert.Triangle.RotatedPrice
/-! Sequential radial asymptotic in drifting direction and varying pair positions. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 390000
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Function Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3

lemma mixed_pattern (K : Matrix I3 I3 ℝ) (s k:ℝ):
 blowThree k s K = -6 * k^3 * s * K.det := by
  have h (i j v) : (∑ m:I3,∑ n:I3,(eps3 i j v:ℝ) * (k*K j m) * (k*K v n) * (∑ t, k * K i t * (eps3 m t n:ℝ) * s))
     = (eps3 i j v:ℝ) * loopSum k s K i j v := by
    unfold loopSum; simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=>Finset.sum_congr rfl fun _ _=>by ring
  have H := eps_nonzero_int
  unfold blowThree; simp_rw [h,triple_inner]
  rw [show (-6:ℝ) * k^3 * s * K.det = ((∑ i:I3,∑ j:I3,∑ n:I3,eps3 i j n * eps3 j i n : ℤ):ℝ) * k^3 * s * K.det by norm_num [H]]
  simp only [Int.cast_sum,Finset.sum_mul, Int.cast_neg,Int.cast_mul] -- simp loop eps_flip! danger
  exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun n _=> by rw [eps_swap12 i j n]; push_cast;ring

section
variable {R : ℕ→ℝ} (hR : Tendsto R atTop atTop) {X Y δ:ℕ→E4} {x y d:E4}
   (hD : Tendsto δ atTop (𝓝 d)) (hU : ∀ n, ‖δ n‖=1) (hx : Tendsto X atTop (𝓝 x)) (hy : Tendsto Y atTop (𝓝 y))
variable {B:ℝ} (hB:8<B) (bx : ∀ k, ‖X k‖ ≤ B/4) (by' : ∀ k, ‖Y k‖ ≤ B/4) (bgap : ∀ k, 1 ≤ ‖X k-Y k‖)
include hR hD hU hx hy hB bx by' bgap
variable (i j k t m n : I3)
local notation "z" => fun ℓ:ℕ=> radial (R ℓ) (δ ℓ)
lemma xy_clear (ℓ) : X ℓ ≠ Y ℓ := fun h=> by have hh := bgap ℓ; exfalso;simp [h] at hh <;> norm_num at hh
lemma limit_clear : x ≠ y := fun h=> by
    have hu : 1 ≤ ‖x-y‖ := ge_of_tendsto (hx.sub hy |>.norm) (Eventually.of_forall bgap)
    simp [h] at hu <;> norm_num at hu
lemma unit_d : ‖d‖=1 := tendsto_nhds_unique hD.norm (by simp [hU])
lemma edge_ne (ℓ) : ‖δ ℓ‖≠0 := (hU ℓ) ▸ one_ne_zero
omit hR hD hU hB bx by'
lemma overlap_as (hxy : x ≠ y) (he : ∀ k, X k ≠ Y k) : Tendsto (fun ℓ => overlap (X ℓ) (Y ℓ)) atTop (𝓝 (overlap x y)) := by simp_rw [overlap_rule (he _),overlap_rule hxy]; exact tendsto_const_nhds.div (hx.sub hy |>.norm.pow 2) (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)))
include hR hD hU hB bx by'
lemma compMP : Tendsto (fun ℓ=> (R ℓ)^4 * mixed i j (radial (R ℓ) (δ ℓ)-(X ℓ))) atTop (𝓝 (mixed i j d)) := by
  have he := hD.sub ((tendsto_inv_atTop_zero.comp hR).smul hx)
  rw [zero_smul,sub_zero] at he
  have H := (mixed_rays i j).diff (x:=d) (by have := unit_d hR hD hU hx hy hB bx by' bgap; rintro rfl;simp at this) |>.continuousAt.tendsto.comp he
  refine H.congr' ((hR.eventually (eventually_gt_atTop (8*B))).mono (fun ℓ hℓ=> ?_))
  dsimp only [comp_apply]
  have e : 0<R ℓ := by linarith
  have hp : R ℓ • (δ ℓ-(R ℓ)⁻¹ • X ℓ) = radial (R ℓ) (δ ℓ) - X ℓ := by rw [smul_sub,smul_inv_smul₀ e.ne'];rfl
  have hu : δ ℓ-(R ℓ)⁻¹ • X ℓ ≠ 0 := fun t=> by have he : radial (R ℓ) (δ ℓ) = X ℓ := sub_eq_zero.mp (hp.symm.trans (by rw [t,smul_zero])); have hz := radialNorm (hU ℓ) e; rw [he] at hz;linarith [bx ℓ]
  rw [←hp]; exact ((mixed_rays i j).stretch hu e.ne').symm
lemma dropPotential (a b:Axis) : Tendsto (fun ℓ => R ℓ^2 * mLine i a (radial (R ℓ) (δ ℓ) - X ℓ)) atTop (𝓝 0) := by
  have he := hD.sub ((tendsto_inv_atTop_zero.comp hR).smul hx)
  rw [zero_smul,sub_zero] at he
  have ht := (mLine_regular i a (u:=d) (by have := unit_d hR hD hU hx hy hB bx by' bgap; rintro rfl;simp at this)).continuousAt.tendsto.comp he
  have hi := (tendsto_inv_atTop_zero.comp hR).mul ht
  rw [zero_mul] at hi
  refine hi.congr' ((hR.eventually (eventually_gt_atTop 0)).mono (fun ℓ hr=> ?_))
  dsimp
  rw [← mLine_energy i a (δ ℓ-(R ℓ)⁻¹ • X ℓ) (R ℓ) hr.ne',smul_sub,smul_inv_smul₀ hr.ne',radial]
  field_simp
lemma coreVanishing : Tendsto (fun ℓ => R ℓ^4 * terminal (X ℓ) (Y ℓ) (radial (R ℓ) (δ ℓ)) i m n) atTop (𝓝 0) := by
  have bgap' ℓ : 1 ≤ ‖Y ℓ-X ℓ‖ := (norm_sub_rev (Y ℓ) (X ℓ)) ▸ (bgap ℓ)
  have Hx := dropPotential hR hD hU hx hy hB bx by' bgap m
  have Hy := dropPotential hR hD hU hy hx hB by' bx bgap' n
  simp_rw [terminal,Finset.mul_sum]
  rw [show (0:ℝ)=∑ _:Axis,∑ _:Axis,0 by simp]
  refine tendsto_finsetSum _ (fun a _ => tendsto_finsetSum _ fun b _=>?_ )
  convert! (tendsto_const_nhds (x:=fan true i a b)).mul ((Hx a b).mul (Hy b a)) using 1
  · ext ℓ; ring
  congr 1;ring
lemma externalLimit :
  Tendsto (fun ℓ=>R ℓ^4 * ∫ w, outerZone i t m n (radial (R ℓ) (δ ℓ)) (X ℓ) (Y ℓ) w) atTop
    (𝓝 (mixed i t d * ∫ w,integralInput t m n x y w)) := by
  have A := limit_clear hR hD hU hx hy hB bx by' bgap
  have Q := xy_clear hR hD hU hx hy hB bx by' bgap
  have h : Tendsto (fun ℓ=> ∫ w, integralInput t m n (X ℓ) (Y ℓ) w) atTop (𝓝 (∫ w,integralInput t m n x y w)) := by simp_rw [flipAverage _ _ _ _ _ A, flipAverage _ _ _ _ _ (Q _)];exact (overlap_as hx hy bgap A Q).const_mul _
  have hd := unit_d hR hD hU hx hy hB bx by' bgap
  have τ := ((mixed_rays i t).diff (x:=d) (by rintro rfl; simp at hd)).continuousAt.tendsto.comp hD
  have hcost := tendsto_finsetSum (ι:=Axis) Finset.univ fun a _=>tendsto_finsetSum (ι:=Axis) Finset.univ fun b _=> (cruxLimit i t a b hR hD hU hx hy B hB bx by' bgap).const_mul (third m t n a b)
  simpa only [mul_zero,Finset.sum_const_zero,add_zero] using ((τ.mul h).add hcost |>.congr' ((hR.eventually (eventually_gt_atTop (2*B))).mono (fun ℓ hr=>(priceCrux i t hR hD hU hx hy B hB bx by' bgap m n ℓ hr).symm)))

lemma reception :
  Tendsto (fun ℓ=>R ℓ^4 * impact (X ℓ) (Y ℓ) (radial (R ℓ) (δ ℓ)) i m n) atTop
   (𝓝 (∑ t:I3, (κ*2*(wind d) i t) * (eps3 m t n:ℝ) * (-(Real.sqrt 2)⁻¹ * overlap x y))) := by
  simp_rw [impact,mul_sub, show ∀ r u :ℝ,r*(2*u)=2*(r*u) from fun _ _=>by ring, Finset.mul_sum] -- typo extra binder
  have H := fun t => ((coreLimit t m n i hR hB (fun k=>(by linarith [bx k])) (fun k=>(by linarith [by' k])) hU).add (externalLimit hR hD hU hx hy hB bx by' bgap i t m n))
  have h := (coreVanishing hR hD hU hx hy hB bx by' bgap i m n).sub (tendsto_finsetSum Finset.univ (fun t _=> (H t).const_mul 2))
  convert! h using 1
  · funext k; simp only [against,mul_add]
  congr 1
  rw [zero_sub,←Finset.sum_neg_distrib]
  unfold wind; apply Finset.sum_congr rfl; intro t ht
  have hu := unit_d hR hD hU hx hy hB bx by' bgap
  rw [tensor_full _ (norm_pos_iff.mp (hu ▸ zero_lt_one)), flipAverage _ _ _ _ _ (limit_clear hR hD hU hx hy hB bx by' bgap), κ,hu]
  norm_num;ring
omit hR hD hU hx hy hB bx by' bgap
lemma blow_pattern (hd : ‖d‖=1) (s : ℝ) : -6*(κ*2)^3*s*(wind d).det = (-6 * κ^3) * s := by rw [det_wind,hd];ring

def stamp := -6 * κ^3 * (-(Real.sqrt 2)⁻¹ * overlap along 0)
omit hR hD hU hx hy hB bx by' bgap
lemma stamp_ne : stamp≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (show κ≠0 from mul_ne_zero (by norm_num) normal_pos.ne'))) (mul_ne_zero (neg_ne_zero.mpr (by positivity)) overlap_ref)
include hR hx hy hD hU hB bx by' bgap in
lemma sphereLimit : Tendsto
  (fun ℓ=> (R ℓ)^12 * classified (X ℓ) (Y ℓ) (radial (R ℓ) (δ ℓ))) atTop (𝓝 (stamp / ‖x-y‖^2)) := by
  have hu := unit_d hR hD hU hx hy hB bx by' bgap
  have hu' (n :ℕ) := (hU n)
  have hd : d≠0 := by rintro rfl; simp at hu
  have hp (i j :I3) := compMP hR hD hU hx hy hB bx by' bgap i j
  have hq (i j :I3) := compMP hR hD hU hy hx hB by' bx (fun ℓ=>by simpa only [norm_sub_rev (Y ℓ)] using (bgap ℓ)) i j
  have hr (i m n:I3) := reception hR hD hU hx hy hB bx by' bgap i m n
  have ep (i m:I3) : mixed i m d = κ*2*wind d i m := by rw [tensor_full _ hd,hu]; unfold κ wind; norm_num;ring; simp
  let s := -(Real.sqrt 2)⁻¹ * overlap x y
  suffices e : Tendsto (fun ℓ=>R ℓ^12 * classified (X ℓ) (Y ℓ) (radial (R ℓ) (δ ℓ))) atTop (𝓝 (blowThree (κ*2) s (wind d))) by
    rw [mixed_pattern, blow_pattern hu] at e
    dsimp only [s] at e
    rw [overlap_rule (limit_clear hR hD hU hx hy hB bx by' bgap)] at e
    convert! e using 1
    congr 1; unfold stamp; ring
  rw [show (fun ℓ:ℕ=> _)=(fun ℓ:ℕ=> ∑ i:I3,∑ j:I3,∑ k:I3,∑ m:I3,∑ n:I3, R ℓ^12*((eps3 i j k:ℝ)*mixed j m (radial (R ℓ) (δ ℓ) - X ℓ)*mixed k n (radial (R ℓ) (δ ℓ) - Y ℓ)* impact (X ℓ) (Y ℓ) (radial (R ℓ) (δ ℓ)) i m n)) from funext fun ℓ=>by simp_rw [classified,Finset.mul_sum],blowThree]
  exact tendsto_finsetSum _ fun i _=>
        tendsto_finsetSum _ fun j _=>
        tendsto_finsetSum _ fun k _=>
        tendsto_finsetSum _ fun m _=>
        tendsto_finsetSum _ fun n _=> show Tendsto _ _ _ from by
          rw [← ep j m, ←ep k n]
          convert! ((((tendsto_const_nhds (x:=(eps3 i j k:ℝ))).mul (hp j m)).mul (hq k n)).mul (hr i m n)) using 1
          · funext ℓ; ring

end
end YM.Pert.Triangle
