import YM.Integration.WilsonPhysicalStationRegisteredDiagonal
import YM.Integration.WilsonPhysicalStationFiledAdjustment

/-! Price for the signed homogeneous registered step, before either endpoint
thermal normalization. All right-hand rates are for the actual two dates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationAdjacentFare
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open PhysicalNext.Repeat.Legato
open WilsonPhysicalStationRegisteredDiagonal (charged ceiling ceiling_nonneg)
open scoped BigOperators Classical Topology
variable {G:Gauge} {h:ℕ} (F:Frame G h)
local notation "μ" => F.coeffSize

theorem salary (x y:F.Coeff): μ x≤μ (x-y)+μ y := by
  simpa using Size.add F (x-y) y

private theorem three (x y z:F.Coeff) : μ (x-z)≤μ (x-y)+μ (y-z) := by
  simpa using Size.add F (x-y) (y-z)

private theorem swap (x y:F.Coeff) : μ (x-y)=μ (y-x) := by
  unfold Frame.coeffSize;apply Finset.sum_congr rfl
  intro i _
  exact norm_sub_rev _ _

def fare (ceiling δ em ek ck:ℝ) : ℝ :=
  (em*(ceiling+δ)+δ)*(1+ek+(1+ck)*ek)+ceiling*((1+ck)*ek)

theorem original (t:ℝ) {em ek ck δ:ℝ} (hm:0≤em) (hδ:0≤δ)
    (a b v u x:F.Coeff)
    (fine:μ (v-a)≤ek*μ v)
    (corr:μ (u-a)≤(1+ck)*ek*μ v)
    (registered:μ (x-F.scaled t u)≤δ*μ u)
    (coarse:μ (x-b)≤em*μ x):
    μ (b-F.scaled t a) ≤ fare (ceiling F t) δ em ek ck*μ v := by
  let z:=F.scaled t
  let c:=ceiling F t
  have hc:0≤c:=ceiling_nonneg F t
  have first:μ a≤(1+ek)*μ v:=by
    have ht:=salary F a v
    rw [swap F a v] at ht
    linarith only [ht,fine]
  have old:μ u≤(1+ek+(1+ck)*ek)*μ v:=by
    have ht:=salary F u a
    linarith only [ht,first,corr]
  have new:μ x≤(c+δ)*μ u:=by
    have ht:=salary F x (z u)
    have soft:=charged F t u
    change μ (z u)≤c*μ u at soft
    linarith only [ht,registered,soft]
  have difference:μ (z u-z a)≤c*μ (u-a):=by rw [←map_sub];exact charged F t _
  have left:μ (b-z u)≤(em*(c+δ)+δ)*μ u:=by
    have ht:=three F b x (z u)
    rw [swap F b x] at ht
    have hcoarse:=coarse.trans (mul_le_mul_of_nonneg_left new hm)
    linarith only [ht,hcoarse,registered]
  have summed:= (three F b (z u) (z a)).trans (add_le_add left difference)
  have all:=add_le_add
    (mul_le_mul_of_nonneg_left old (add_nonneg (mul_nonneg hm (add_nonneg hc hδ)) hδ))
    (mul_le_mul_of_nonneg_left corr hc)
  exact summed.trans (all.trans_eq (by unfold fare;dsimp [c];ring))

end YM.Integration.WilsonPhysicalStationAdjacentFare
end
