import YM.RG11Proof.Rigidity.Meeting

/-!
# Arctic blast at a double B probe
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Tensor Analysis Maxwell Maxwell.Free Extra.FD.SphereTest Filter Set Function
open scoped BigOperators Topology ContDiff Classical
open Crowd
variable {G : Gauge}

-- First expose the absence of that pole (requiring a family of MOMENT
-- identities on the very same deficit W, no positivity or Gram premises).
def Chill (S : Finset E4) (W : Crowd G) : Prop := W.Live S ∧ W.asks meter=0 ∧
    ∀ (a b c : Foil) (y z : E4), y≠z → y∉S → z∉S → ((panel W (same z b c)).panel (same y a a)).asks meter=0

namespace Chill
variable {W : Crowd G} {S : Finset E4}

lemma flake (H : Chill S W) {z : E4} (hz : z∉S) {x : E4} (h : z+x∉S) (hx : x≠0) (a b c : Foil) :
   rotor x a b * splitAt W (z+x) z a c + rotor x a c * splitAt W (z+x) z a b =
    qRad x^3 * (-((8*normal:ℝ))⁻¹ * coldAt W (z+x) z a b c) := by
  have hm := (profile_cold H.2.1 a b c (z+x) z).symm.trans
    (H.2.2 a b c (z+x) z (by simpa using hx) h hz)
  rw [add_sub_cancel_left,beam,beam,if_neg hx,if_neg hx] at hm
  have ht : qRad x≠0 := (pow_pos (norm_pos_iff.mpr hx) _).ne'
  have hp := normal_pos
  field_simp at *
  linear_combination hm

-- Elementary elimination of coefficients without having to divide in a
-- ring of coordinate functions (especially good on slots sharing an axis).
private lemma row {t : Foil} {P U : Foil → ℝ} {q c : ℝ} {R : Foil→Foil→ℝ}
    (h : ∀ b d : Foil, U b*P d + U d*P b=q^3*(c*R b d))
    (hs : ∑ b : Foil, U b^2 = 2*q^2) (hq : q≠0) :
     P t = q * (1/2*c * ∑ b : Foil, (U b*R b t-1/2*U t*R b b)) := by
  have he (b) : U b^2*P t=q^3*c*(U b*R b t-1/2*U t*R b b) := by
    linear_combination U b * h b t - 1/2 * U t * h b b
  have ht := Finset.sum_congr (s₁:=(Finset.univ : Finset Foil)) rfl (fun i _=> he i)
  rw [← Finset.sum_mul,hs,← Finset.mul_sum] at ht
  apply mul_left_cancel₀ (pow_ne_zero 2 hq)
  linear_combination ht/2

def debris (W : Crowd G) (z : E4) (a t : Foil) (x : E4) :=
    1/2*(-(8*normal:ℝ)⁻¹) * ∑ b : Foil, (rotor x a b * coldAt W (z+x) z a b t-1/2*rotor x a t*coldAt W (z+x) z a b b)

lemma thaws (H : Chill S W) {z : E4} (hz : z∉S) {a t : Foil} (ha : a.1≠a.2) :
    (fun x=> splitAt W (z+x) z a t) =ᶠ[𝓝 0] qRad • debris W z a t := by
  have hq : ContDiffAt ℝ ω (debris W z a t) 0 := by
    apply contDiffAt_const.mul (ContDiffAt.sum _)
    intro j _
    exact ((rotor_good a j).contDiffAt.mul (cold_diff H.1 _ _ _ hz)).sub
      ((contDiffAt_const.mul (rotor_good a t).contDiffAt).mul (cold_diff H.1 _ _ _ hz))
  have hv : (fun x=> splitAt W (z+x) z a t) =ᶠ[𝓝[≠] 0] qRad • debris W z a t := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (naked hz)] with x hx he
    exact row (fun b d=>H.flake hz he hx a b d) (full_row x a ha) (show qRad x ≠0 from (pow_pos (norm_pos_iff.mpr hx) _).ne')
  have hc := (split_ghost H.1 a t z).thin 0 (by simpa [bare])
  -- extend punctured Eq to ambient smooth germ
  have hp : NeBot (𝓝[≠] (0:E4)) := inferInstance
  have hk : splitAt W z z a t = qRad 0 * debris W z a t 0 := by
    have Ht : Tendsto qRad (𝓝[≠] (0:E4)) (𝓝 (qRad 0)) := (pure_square.smooth.continuous.tendsto _).mono_left nhdsWithin_le_nhds
    have Hr : Tendsto (qRad • debris W z a t) (𝓝[≠] (0:E4)) (𝓝 (qRad 0 * debris W z a t 0)) :=
      Ht.mul (hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    simpa using tendsto_nhds_unique ((hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hv) Hr
  rw [← nhdsNE_sup_pure (0:E4)]
  exact eventually_sup.mpr ⟨hv,by simpa using hk⟩

lemma hail (H : Chill S W) {z : E4} (hz : z∉S) (a t : Foil) {y : E4} (hy : y∉S) : splitAt W y z a t=0 := by
  by_cases ha : a.1=a.2
  · unfold splitAt splitP pulls; simp_rw [toss_dead a ha,zero_mul,Finset.sum_const_zero,ask_const_zero,Finset.sum_const_zero]
  have hq : ContDiffAt ℝ ∞ (debris W z a t) 0 := by
    apply contDiffAt_const.mul (ContDiffAt.sum _)
    intro j _
    exact (((rotor_good a j).of_le le_top).contDiffAt.mul ((cold_diff H.1 _ _ _ hz).of_le le_top)).sub
      ((contDiffAt_const.mul ((rotor_good a t).of_le le_top).contDiffAt).mul ((cold_diff H.1 _ _ _ hz).of_le le_top))
  have hh := (split_ghost H.1 a t z).gone (naked hz) _ hq (thaws H hz ha)
  have he : z+(y-z)=y := by abel
  have hv := hh (x:=y-z) (by simpa [bare,he])
  simpa [he] using hv

lemma biloc (H : Chill S W) {y z : E4} (ha : y∉S) (hb : z∉S) (a b : Foil) :
    (W.panel ((a,y),b,z)).asks meter=0 := by rw [profile_split H.2.1,H.hail hb a b ha]
end Chill
end YM.RG11.Rigidity
