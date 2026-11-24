import YM.SchemeRG11.Storm.Braid
/-!
Two independent gradient legs. Keep apex subtraction with arbitrary smooth volume
profile -- here radial ball. Values delivered inside & outside.
-/
set_option autoImplicit false
set_option maxHeartbeats 370000
noncomputable section
namespace YM.SchemeRG11.Storm
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
variable (i j : Eye)(a b : Axis)(z x y:E4)
local notation "V" => zone z x y

def twigs (w:E4):= Steam.score [a] (x-w)*Steam.score [b] (y-w)
def petal (w:E4):= mixed i j (z-w)*(twigs a b x y w-twigs a b x y z)
def pollen (w:E4):=mixed i j (z-w)*twigs a b x y w
def savour : ℝ:= (∫ w in V, petal i j a b z x y w)+(∫ w in (V)ᶜ,pollen i j a b z x y w)
local notation "tree" => (volume.restrict tripod)
local notation "Gig" => atopin i j a b z x y
local notation "Fib" => atopout i j a b z x y
lemma ferries {w:E4} (hx:x≠w) (hy:y≠w) : (∫ q,hedge a b x y q w ∂Zen.prod Zen)=twigs a b x y w := by
   unfold hedge; rw [integral_prod_mul (fun t=>Steam.tint [a] t (x-w)) (fun t=>Steam.tint [b] t (y-w)), show Zen=volume.restrict openZen from rfl,sculpt _ _ (sub_ne_zero.mpr hx),sculpt _ _ (sub_ne_zero.mpr hy)]; rfl

variable {x y z} (hx:z≠x)(hy:z≠y)(H:x≠y)
include hx hy
lemma gold : (fun w:E4=>∫ p, (atopin i j a b z x y) (w,p) ∂tree) =ᵐ[volume.restrict V] petal i j a b z x y := by
  filter_upwards [ae_restrict_mem (show MeasurableSet V from isClosed_closedBall.measurableSet), ae_restrict_of_ae (μ:=volume) (volume.ae_ne z)] with w hw he
  have hh:=zone_separated hx hy hw
  rw [tree_m]
  dsimp only [atopin]
  have hk (v:E4) (hh:x≠v)(hp:y≠v) : Integrable (fun p=>hedge a b x y p v) (Zen.prod Zen):=(tint_i [a] (sub_ne_zero.mpr hh)).mul_prod (tint_i [b] (sub_ne_zero.mpr hp))
  rw [integral_prod_mul (fun t=> fused true i false j t (z-w)) (fun q=> hedge a b x y q w - hedge a b x y q z), integral_sub (hk w hh.1.symm hh.2.symm) (hk z hx.symm hy.symm),ferries a b x y hh.1.symm hh.2.symm,ferries a b x y hx.symm hy.symm, show Zen=volume.restrict openZen from rfl, ← mixed_heat i j (sub_ne_zero.mpr (show z≠w from Ne.symm he))]; rfl
omit hx hy in
lemma nectar {x y z:E4}: (fun w:E4=>∫ p, (atopout i j a b z x y) (w,p) ∂tree) =ᵐ[volume.restrict (V)ᶜ] pollen i j a b z x y := by
  filter_upwards [ae_restrict_of_ae (μ:=volume) (s:=(V)ᶜ) (volume.ae_ne z),ae_restrict_of_ae (μ:=volume) (volume.ae_ne x),ae_restrict_of_ae (μ:=volume) (volume.ae_ne y)] with w hw hu hv
  rw [tree_m]; dsimp only [atopout]; rw [integral_prod_mul (fun t=> fused true i false j t (z-w)) (fun q=> hedge a b x y q w),ferries a b x y (Ne.symm hu) (Ne.symm hv), show Zen=volume.restrict openZen from rfl, ← mixed_heat i j (sub_ne_zero.mpr (show z≠w from Ne.symm hw))]; rfl

lemma petals : IntegrableOn (petal i j a b z x y) V := Integrable.congr ((bud i j a b hx hy).integral_prod_left ..) (gold i j a b hx hy)
include H
lemma pollens : IntegrableOn (pollen i j a b z x y) (V)ᶜ := Integrable.congr ((twig i j a b hx hy H).integral_prod_left ..) (nectar i j a b)

lemma field : savour i j a b z x y= ∫ p, (∫ w,(atopout i j a b z x y (w,p))) ∂tree := by
  unfold savour
  have hi:=bud i j a b hx hy; have he:=twig i j a b hx hy H
  rw [← integral_congr_ae (gold i j a b hx hy),← integral_congr_ae (nectar i j a b),← integral_prod _ hi,← integral_prod _ he]
  rw [integral_prod_symm Gig hi, integral_prod_symm Fib he, ←integral_add hi.integral_prod_right he.integral_prod_right]
  refine integral_congr_ae (ae_restrict_of_forall_mem tripod_meas (fun p hp=>?_))
  let F (w:E4):= atopout i j a b z x y (w,p)
  have hf : Integrable F volume:= by
     unfold F atopout fused
     simp only [neg_mul, Finset.sum_mul]
     refine (Integrable.neg (integrable_finsetSum _ (fun u _=> integrable_finsetSum _ (fun v _=>?_))))
     have hh : Integrable (fun w=> rotatedProduct true i false j u v * juice [u,v] [a] [b] p (castEye z x y) w) volume := (juice_cost [u,v] [a] [b] p hp (castEye z x y)).const_mul _
     convert! hh using 1; ext w; change Steam.tint _ _ _ * _ * (Steam.tint [a] p.2.1 (x-w)*Steam.tint [b] p.2.2 (y-w))= _*(Steam.tint [u,v] p.1 (z-w)*Steam.tint [a] p.2.1 (x-w)*Steam.tint [b] p.2.2 (y-w)); ring
  have hm : MeasurableSet V:= isClosed_closedBall.measurableSet
  have hz : IntegrableOn (fun w:E4=> fused true i false j p.1 (z-w)*hedge a b x y p.2 z) V := ((fuse_position ..).continuous.comp (g:=fused true i false j p.1) (f:=fun w:E4=>z-w) (by fun_prop)|>.mul_const _).continuousOn.integrableOn_compact (isCompact_closedBall ..)
  change (∫ w in V, atopin _ _ _ _ _ _ _ (w,p))+(∫ w in (V)ᶜ,F w)=∫ w,F w
  rw [← integral_add_compl hm hf]; change (∫ w in V,fused true i false j p.1 (z-w)*(hedge a b x y p.2 w - hedge a b x y p.2 z))+(∫ w in (V)ᶜ,F w)=_
  congr 1; simp only [mul_sub]; change (∫ w in V,F w-fused true i false j p.1 (z-w)*hedge a b x y p.2 z)=_; rw [integral_sub hf.integrableOn hz, integral_mul_const, show (∫ w in V,fused true i false j p.1 (z-w))=0 from keys i j p.1 (pairHole z x y) z,zero_mul,sub_zero]

lemma organ (X : Nodes 4) (ht:X=castEye z x y):
   savour i j a b z x y= -(∑ u,∑ v,rotatedProduct true i false j u v*yolk [u,v] [a] [b] X) := by
  rw [field i j a b hx hy H]; unfold yolk; subst X
  let F:= fun u v (p:Time)=> rotatedProduct true i false j u v*orb [u,v] [a] [b] p (castEye z x y)
  have hi u v: Integrable (F u v) tree := (oak [u,v] [a] [b] (pantry hx H hy)).const_mul _
  simp only [← integral_const_mul]
  change (∫ p in tripod,_) = -(∑ u,∑ v, ∫ p in tripod,F u v p)
  simp_rw [← show ∀ u, (∫ p in tripod, ∑ v,F u v p)=_ from fun u=> integral_finsetSum _ (fun v _=>hi u v)]
  rw [← integral_finsetSum _ (fun u _=> integrable_finsetSum _ (fun v _=>hi u v)),←integral_neg]
  refine integral_congr_ae (ae_restrict_of_forall_mem tripod_meas (fun p hp=>?_))
  let G (u v : Axis) (w : E4):= rotatedProduct true i false j u v*juice [u,v] [a] [b] p (castEye z x y) w
  have he u v : Integrable (G u v) volume := (juice_cost [u,v] [a] [b] p hp _).const_mul _
  have hk (w:E4) : atopout i j a b z x y (w,p)= -(∑ u,∑ v,G u v w):= by
    simp only [atopout,fused,neg_mul,Finset.sum_mul]; congr 1; apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _; change Steam.tint _ _ _ * _ * (Steam.tint [a] p.2.1 (x-w)*Steam.tint [b] p.2.2 (y-w))= _*(Steam.tint [u,v] p.1 (z-w)*Steam.tint [a] p.2.1 (x-w)*Steam.tint [b] p.2.2 (y-w)); ring
  dsimp only
  simp only [hk]; rw [integral_neg,integral_finsetSum _ (fun u _=> integrable_finsetSum _ (fun v _=>he u v))]; congr 1
  apply Finset.sum_congr rfl; intro u _
  rw [integral_finsetSum _ (fun v _=> he u v)]; apply Finset.sum_congr rfl; intro v _; unfold F G; rw [grape _ _ _ _ hp,integral_const_mul]
end YM.SchemeRG11.Storm
