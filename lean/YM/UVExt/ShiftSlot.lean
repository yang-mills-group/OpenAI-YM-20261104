import YM.UVExt.SlotJet

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Function Lattice Laurent Wilson Bloch Exterior Precision RG Bid NormedSpace
open scoped Classical Topology BigOperators ComplexConjugate ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (v : Dir G n)
local notation "𝒱" => G.Mat
local notation "D₀" => dColor G n 1
local notation "D" => ‖dColor G n 1 v‖

section generic
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] {a b q f : ℝ → E} (hf : ContDiff ℝ ω f) (ha : ContDiff ℝ ω a) (hb : ContDiff ℝ ω b) (hg : ContDiff ℝ ω q)
    (hz : a 0 = 0) (h0 : b 0=0) (hz2 : q 0=0) (hf0 : f 0=1)
include ha hb hz h0 in
lemma two_vanish : iteratedDeriv 2 (a*b) 0 = 2 • (iteratedDeriv 1 a (0:ℝ) * iteratedDeriv 1 b 0) := by
  rw [iteratedDeriv_mul (𝔸:=E) (f:=a) (g:=b) ((ha.of_le (show ((2:ℕ):WithTop ℕ∞) ≤ ω by simp)).contDiffAt) ((hb.of_le (show ((2:ℕ):WithTop ℕ∞) ≤ ω by simp)).contDiffAt)]
  simp [Finset.sum_range_succ,hz,h0,nsmul_eq_mul,mul_assoc]

include hf ha hz hf0 in
private lemma first_unit : iteratedDeriv 1 (a*f) 0 = iteratedDeriv 1 a 0 := by
  simp [iteratedDeriv_one,deriv_mul (𝔸:=E) (x:=0) (𝕜:=ℝ) (ha.differentiable (by simp) _) (hf.differentiable (by simp) _),hz,hf0]
include hf ha hz hf0 in
private lemma left_unit : iteratedDeriv 1 (f*a) 0 = iteratedDeriv 1 a 0 := by
  simp [iteratedDeriv_one,deriv_mul (𝔸:=E) (𝕜:=ℝ) (x:=0) (hf.differentiable (by simp) _) (ha.differentiable (by simp) _),hz,hf0]
-- if near inputs, previous purchases stay real.
include hf ha hb hz h0 hf0 in
lemma two_units : iteratedDeriv 2 (f*(a*b)) 0=2 • (iteratedDeriv 1 a 0 * iteratedDeriv 1 b 0) ∧
    iteratedDeriv 2 ((a*b)*f) 0=2 • (iteratedDeriv 1 a 0 * iteratedDeriv 1 b 0) := by
  rw [←two_vanish ha hb hz h0,←mul_assoc, mul_assoc a b f]
  rw [two_vanish ha hb hz h0, two_vanish (a:=f*a) (hf.mul ha) hb (by simp [hz]) h0, two_vanish (b:=b*f) ha (hb.mul hf) hz (by simp [h0]), first_unit hf hb h0 hf0, left_unit hf ha hz hf0]
  trivial
end generic

variable {L : ℝ}
lemma curve_delta {a b : Walk} (ha : (a.length + b.length:ℝ) ≤ L) (h : stop (0:Cover) a=stop 0 b) (x : Site n) :
    ‖iteratedDeriv 1 (curve v a x - curve v b x) 0‖ ≤ G.colorScale * L^2 * D := by
  have hh : iteratedDeriv 1 (curve v a x - curve v b x) 0=G.colorMat (linkSum (collect G v) x a - linkSum (collect G v) x b) := by
    rw [iteratedDeriv_one]
    change deriv ((fun t=>G.mat (travel (represent (t • v)) x a)) - (fun t=> G.mat (travel (represent (t • v)) x b))) 0=_
    rw [map_sub]; convert ((Push.travell a x v).sub (Push.travell b x v)).deriv using 1
  rw [show iteratedDeriv (𝕜:=ℝ) (F:=G.Mat) 1 (curve v a x - curve v b x) 0 = _ from hh, G.colorMat_norm,mul_assoc] 
  have hz := ribbon v (RG.Slot.mk a ⟨⟨0,1⟩,by decide⟩) (RG.Slot.mk b ⟨⟨0,1⟩,by decide⟩) h x
  push_cast at hz
  exact mul_le_mul_of_nonneg_left (hz.trans (by exact mul_le_mul_of_nonneg_right (by gcongr) (norm_nonneg _) )) G.colorScale_pos.le

lemma operator_shift (t u g : ℝ→𝒱) (ht : ContDiff ℝ ω t) (hu : ContDiff ℝ ω u) (hg : ContDiff ℝ ω g) (hT : t 0=1) (hV : u 0=1)
    (hz : g 0=0) : ‖iteratedDeriv 2 (t*g*star t-u*g*star u) 0‖ ≤
    4 * ‖iteratedDeriv 1 (t-u) 0‖ * ‖iteratedDeriv 1 g 0‖ := by
  let S := (starL ℝ : 𝒱≃L[ℝ]𝒱).toContinuousLinearMap
  have he (a : ℝ→𝒱) : star a = S ∘ a := rfl
  have hC (a : ℝ→𝒱) (h : ContDiff ℝ ω a) : ContDiff ℝ ω (star a) := by rw [he]; exact S.contDiff.comp h
  have hm {a : ℝ→𝒱} : star a 0 = S (a 0) := rfl
  rw [show t*g*star t-u*g*star u=(t-u)*g*star t + u*(g*star (t-u)) by rw [show star (t-u)=star t-star u from star_sub ..]; noncomm_ring] -- smul
  have ha : (t-u) 0=0 := by simp [*,hT,hV]
  rw [show iteratedDeriv 2 ((t-u)*g*star t+u*(g*star (t-u))) 0 = _ from iteratedDeriv_add (n:=2) (x:=(0:ℝ)) (((ht.sub hu |>.mul hg).mul (hC t ht)).of_le (by simp)|>.contDiffAt) ((hu.mul (hg.mul (hC _ (ht.sub hu)))).of_le (by simp)|>.contDiffAt),
     (two_units (E:=𝒱) (a:=t-u) (hC t ht) (ht.sub hu) hg ha hz (by rw [hm,hT]; exact star_one 𝒱)).2,(two_units (E:=𝒱) (b:=star (t-u)) hu hg (hC (t-u) (ht.sub hu)) hz (by rw [hm,ha,map_zero]) hV).1]
  have hS : iteratedDeriv 1 (star (t-u)) 0 = S (iteratedDeriv 1 (t-u) 0) := by rw [he]; exact linear_successor (ht.sub hu) S _ _
  rw [hS]
  refine (norm_add_le ..).trans ?_
  refine le_trans (add_le_add (show _ from norm_nsmul_le (n:=2)) (show _ from norm_nsmul_le (n:=2))) ?_
  simp only [Nat.cast_ofNat]
  change 2 * ‖(iteratedDeriv 1 (t-u) 0 * iteratedDeriv 1 g 0)‖ + 2 * ‖(iteratedDeriv 1 g 0 * star (iteratedDeriv 1 (t-u) 0))‖ ≤ _
  linarith only [norm_mul_le (iteratedDeriv 1 (t-u) 0) (iteratedDeriv 1 g 0), show _ from (norm_mul_le (iteratedDeriv 1 g 0) (star (iteratedDeriv 1 (t-u) 0))).trans_eq (by rw [norm_star])]

lemma second_space (x : Site n) (a b : Slot) (hb : (a.walk.length+b.walk.length:ℝ) ≤ L) (hf : a.offset=b.offset) (hxy : a.plaq=b.plaq) :
    ‖iteratedDeriv 2 (scion v x a - scion v x b) 0‖ ≤ 4* G.colorScale^2 * L^2 * D^2 := by
  let z := Work.F03.slotFace a x
  let A (t : ℝ) := faceValue (represent (t • v)) z
  let g (t:ℝ) := G.colorMat (G.curvature (A t))
  have hb' : Work.F03.slotFace b x=z := Prod.ext (congr_arg (wrap n · + x) hf.symm) hxy.symm
  let r (a : Walk) := curve v a x
  have hr t i : scion v x t i=(r t.walk i) * (G.colorMat (G.curvature (faceValue (represent (i • v)) (Work.F03.slotFace t x)))) * star (r t.walk i) := by
      unfold scion bud; dsimp only [Function.comp_apply]; rw [Work.F03.atSite_path]; exact G.mat_adjoint _ _
  have hd : scion v x a-scion v x b = r a.walk*g*star (r a.walk) - r b.walk*g*star (r b.walk) := by ext i j k; simp only [Pi.sub_apply,Pi.star_apply,Pi.mul_apply,hr,hb']; congr! <;> (try rfl)
  have ha0 : A 0=1 := by unfold A faceValue; rw [zero_smul]; exact Push.stroll_zero ..
  let p := RG.Slot.mk [] a.plaq
  have hi t : G.curvature (A t)=bud v (wrap n a.offset + x) p t := by
    rw [bud, Work.F02.atSite_curvature]; rfl
  have ht1 : HasDerivAt g (G.colorMat (Work.F03.faceCurl z v)) 0 := G.colorMat.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt _ (Work.F03.curvature_of_hasDerivAt (Work.F03.face_deriv z v))
  have h1 : ‖iteratedDeriv 1 g 0‖ ≤ G.colorScale * D := by rw [iteratedDeriv_one,ht1.deriv,G.colorMat_norm]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (dColor G n 1 v) (z.1,plaquette z.2)) G.colorScale_pos.le
  let H := G.colorScale
  let u := r b.walk; let t := r a.walk
  have ht2 : ‖iteratedDeriv 1 (t-u) 0‖ ≤ H * L^2 * D := curve_delta v hb hf _
  let C : ℝ := 4*‖iteratedDeriv 1 (t-u) 0‖*‖iteratedDeriv 1 g 0‖
  refine le_trans ?_ (show C ≤ _ from ?_)
  · rw [hd]; unfold C; apply operator_shift (G:=G) _ _ g (curve_smooth ..) (curve_smooth ..)
    · change ContDiff ℝ ω (fun t=> G.colorMat (G.curvature (A t))); simp_rw [hi]; exact ContDiff.comp (G.colorMat.toContinuousLinearMap.contDiff) (bud_smooth ..)
    · unfold curve; rw [zero_smul,Push.stroll_zero,G.mat_one]
    · unfold curve; rw [zero_smul,Push.stroll_zero,G.mat_one]
    · unfold g; rw [ha0,G.curvature_unit]; exact map_zero G.colorMat
  exact (mul_le_mul (mul_le_mul_of_nonneg_left ht2 (by norm_num : (0:ℝ) ≤ 4)) h1 (norm_nonneg _) (by positivity [G.colorScale_pos])).trans_eq (by change 4*(G.colorScale*L^2*D) * (G.colorScale*D) = _; ring)



def partMat (G : Gauge) (i : G.ColorIndex) := (part (G:=G) i).comp G.projectColor.toContinuousLinearMap

def curveBill (G : Gauge) := K G + 4 * G.colorScale^2 * ∑ i, magnitude (partMat G i)
lemma curveBill_ge (G : Gauge) : K G ≤ curveBill G := le_add_of_nonneg_right (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _=>by exact ContinuousLinearMap.opNorm_nonneg (partMat G i)))
lemma curveBill_pos (G : Gauge) : 1 ≤ curveBill G := (K_pos G).trans (curveBill_ge G)
lemma curveBill_large (i : G.ColorIndex) : magnitude (partMat G i)*4*G.colorScale^2 ≤ (curveBill G)^2 := by
  refine le_trans ?_ (le_self_pow₀ (curveBill_pos G) (by decide : (2:ℕ)≠0))
  calc
    _ = 4 * G.colorScale^2 * magnitude (partMat G i) := by ring
    _ ≤ curveBill G := by unfold curveBill; exact le_add_of_nonneg_of_le (zero_le_one.trans (K_pos G)) (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j (_:j∈Finset.univ) => by exact ContinuousLinearMap.opNorm_nonneg (partMat G j)) (Finset.mem_univ i)) (by positivity))

lemma scion_smooth (z a) : ContDiff ℝ ω (scion v z a) := ContDiff.comp G.colorMat.toContinuousLinearMap.contDiff (bud_smooth ..)
lemma scion_part (x a i) : sprout v x a i = partMat G i ∘ scion v x a := funext fun t => by
  change part i (bud v x a t)=part i (G.projectColor (G.colorMat _))
  rw [Gauge.project_colorMat]

lemma part_difference_rate {a b : Slot} (hb : (a.length+b.length:ℝ) ≤ L) (hf : a.offset=b.offset) (hxy : a.plaq=b.plaq) x i : Quad (2*tempo v L) ((curveBill G)*L*D) (sprout v x a i - sprout v x b i) := by
  let Y := sprout v x a i - sprout v x b i
  let T := scion v x a - scion v x b
  have ha := hb.trans' (show (a.length:ℝ) ≤ a.length+b.length by exact le_add_of_nonneg_right (Nat.cast_nonneg _))
  have ht := hb.trans' (show (b.length:ℝ) ≤ a.length+b.length by exact le_add_of_nonneg_left (Nat.cast_nonneg _))
  have he := (sprout_bill v x a i L ha).1.minus (sprout_bill v x b i L ht).1 zero_lt_one
  have hT := (scion_smooth v x a).sub (scion_smooth v x b)
  have hQ : Y=partMat G i ∘ T := funext fun c => (by simp [Y,scion_part,T, Function.comp_apply])
  have h : Work.F03.slotFace a x=Work.F03.slotFace b x := Prod.ext (congr_arg (wrap _ ·+x) hf) hxy
  refine ⟨⟨he.pos,he.smooth,he.pay,fun k hk=> ?_⟩,?_⟩
  · by_cases hi : k=0
    · subst k; exact he.vanish _ zero_lt_one
    obtain rfl := show k=1 by omega
    rw [iteratedDeriv_sub (n:=1) ((sprout_diff v x a i).of_le (show ((1 : ℕ∞):WithTop ℕ∞) ≤ ω by simp)).contDiffAt ((sprout_diff v x b i).of_le (by simp)).contDiffAt, iteratedDeriv_one,iteratedDeriv_one, sprout_first,sprout_first,h,sub_self]
  rw [←Real.norm_eq_abs]; change ‖iteratedDeriv 2 Y 0‖ ≤ _; rw [hQ, show iteratedDeriv 2 (partMat G i ∘ T) 0= _ from linear_successor (X:=𝒱) hT (partMat G i) (2:ℕ) (0:ℝ)]
  have hz := ((partMat G i).le_opNorm (iteratedDeriv 2 T 0))
  have hu := second_space v x a b (show (a.walk.length+b.walk.length:ℝ)≤L by unfold Slot.length at hb; push_cast at *; linarith) hf hxy
  calc
     _ ≤ magnitude (partMat G i) * ‖iteratedDeriv 2 T 0‖ := hz
     _ ≤ magnitude (partMat G i)* (4*G.colorScale^2*L^2*D^2) := mul_le_mul_of_nonneg_left hu (show _ from ContinuousLinearMap.opNorm_nonneg (partMat G i))
     _ = (magnitude (partMat G i)*4*G.colorScale^2)*(L*D)^2 := by ring
     _ ≤ ((curveBill G)*L*D)^2 := by simpa only [mul_assoc,← mul_pow] using mul_le_mul_of_nonneg_right (curveBill_large i) (sq_nonneg (L*D))

end YM.UVExt.Paths
