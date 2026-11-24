import YM.Integration.ActualTrajectoryTransport
import YM.Integration.ActualWilsonConditionalRoots

/-! The physical clock transports a signed error with its two original first moments. -/
noncomputable section
namespace YM.Integration.WilsonCoherentEarlier
open MeasureTheory Wilson RG
open scoped Classical
variable {G:Gauge} (C:Family G) (hc:C.Makes) {N per j m:ℕ}
include hc

theorem averaged (hj:j<N) {f:Config G (C.side (j+1) per)→ℝ} (h:Envelope f) :
    Envelope (actualAverage C (N:=N) f) := by
  have w:=ActualWilsonConditionalRoots.density_meas C (p:=per) hc hj
  have hf:Measurable (fun z:Config G (C.side j per) × Config G (C.side (j+1) per) =>
      actualConditionalDensity C N per j z.1 z.2 * f z.2):=w.mul (h.meas.comp measurable_snd)
  obtain ⟨K,hK⟩:=h.cost
  exact ⟨hf.stronglyMeasurable.integral_prod_right'.measurable,K,
    actualAverage_norm_le C hc hj hK⟩

theorem envelope (hj:j≤N) {f:Config G (C.side j per)→ℝ} (hf:Envelope f) (hm:m≤j) :
    Envelope (actualTransport C (N:=N) f hm) := by
  induction hm using Nat.decreasingInduction with
  | self => rwa [actualTransport_base C hc hj]
  | of_succ k hk ih =>
    rw [actualTransport_step C hc hj f hk]
    exact averaged C hc (hk.trans_le hj) ih

theorem step (hj:j<N) {f h a b:Config G (C.side (j+1) per)→ℝ} (f0:Envelope f)
    (h0:Envelope h) (a0:Envelope a) (b0:Envelope b) {x y:ℝ}
    (small:∀U, |f U-h U|≤x*a U+y*b U) (V:Config G (C.side j per)) :
    |actualAverage C (N:=N) f V-actualAverage C (N:=N) h V| ≤
      x*actualAverage C (N:=N) a V+y*actualAverage C (N:=N) b V := by
  let μ:=prior G (C.side (j+1) per)
  let w:=actualConditionalDensity C N per j V
  have neg (u):0≤w u:=actualConditionalDensity_nonneg C hc hj V u
  have integr {u:Config G (C.side (j+1) per)→ℝ} (hu:Envelope u) :
      Integrable (fun v=>w v*u v) μ:=by
    obtain ⟨K,hK⟩:=hu.cost
    exact actualAverage_integrable C hc hj hu.meas.aestronglyMeasurable hK V
  have fi:=integr f0
  have hi:=integr h0
  have ai:=integr a0
  have bi:=integr b0
  change |(∫u,w u*f u ∂μ)-(∫u,w u*h u ∂μ)| ≤ x*(∫u,w u*a u ∂μ)+y*(∫u,w u*b u ∂μ)
  rw [←integral_sub fi hi,←integral_const_mul,←integral_const_mul,←integral_add (ai.const_mul x) (bi.const_mul y)]
  apply le_trans (norm_integral_le_integral_norm _) (integral_mono (fi.sub hi).norm ((ai.const_mul x).add (bi.const_mul y)) ?_)
  intro u
  change |w u*f u-w u*h u|≤x*(w u*a u)+y*(w u*b u)
  rw [←mul_sub,abs_mul,abs_of_nonneg (neg u)]
  calc _ ≤ w u*(x*a u+y*b u):=mul_le_mul_of_nonneg_left (small u) (neg u)
       _ = _ :=by ring

theorem signed (hj:j≤N) {f h a b:Config G (C.side j per)→ℝ} (f0:Envelope f)
    (h0:Envelope h) (a0:Envelope a) (b0:Envelope b) {x y:ℝ}
    (small:∀U, |f U-h U|≤x*a U+y*b U) (hm:m≤j) (V:Config G (C.side m per)) :
    |actualTransport C (N:=N) f hm V-actualTransport C (N:=N) h hm V| ≤
      x*actualTransport C (N:=N) a hm V+y*actualTransport C (N:=N) b hm V := by
  induction hm using Nat.decreasingInduction with
  | self => simpa only [actualTransport_base C hc hj] using small V
  | of_succ k hk ih =>
    simpa only [actualTransport_step C hc hj _ hk] using
      step C hc (hk.trans_le hj) (envelope C hc hj f0 hk) (envelope C hc hj h0 hk)
        (envelope C hc hj a0 hk) (envelope C hc hj b0 hk) ih V

end YM.Integration.WilsonCoherentEarlier
