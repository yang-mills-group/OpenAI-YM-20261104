import YM.LocalLTE.Frame.Canon
import YM.LocalLTE.Inset.Cobalt
/-! Prices for mapping to a canonical chart from an AUXILIARY logarithm
(note torus extent paid). Requires only the *existence* of SOME modest
direction (not a choice of smooth gauge delivered ahead based on previous
orientation). All derivatives through comparison order. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Frame
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L c f : Side} {j n : ℕ} {a Y d₀ d v : ℝ} {U:Config G c}
local notation "E" => Positions (Uniform.Primary c G)
local notation "r" => Blaze.royalty G
abbrev chainT (u:G.El)(V:Config G c) := gauge (fun _=>u) (root V)
lemma modeLift (i:Site c) : separation 0 i ≤ c.val := by
  unfold separation Lattice.pdist; apply Finset.sup_le; intro j _; have h:=lift_centers (0-i) j; omega
lemma anchorFee (ha : (c.val:ℝ) ≤ a) (i:Site c): ((carriage 0 i).length:ℝ)≤4*a := by
  apply le_trans (b:=↑(4*c.val:ℕ)) ?_ (by push_cast; linarith); exact_mod_cast (mileage 0 i).trans (Nat.mul_le_mul_left 4 (modeLift i))
lemma minorChord (h : (c.val:ℝ) ≤ a) (hf : 0 ≤ Y) (hp : ∀ i,G.chord (U i)≤ Y) (u:G.El)(i : Bond c):
    G.chord (chainT u U i) ≤ (8*a+1)*Y:= by
  have he (j : Site c) : G.chord (carrier 0 U j) ≤ 4*a*Y:= (travel_chord U (carriage 0 j) 0 Y hp).trans (mul_le_mul_of_nonneg_right (anchorFee h _) hf)
  unfold chainT Lattice.gauge; rw [G.chord_conj]
  change G.chord (carrier 0 U i.1 * U i * (carrier 0 U _)⁻¹)≤ _
  refine (G.chord_triangle ..).trans ?_; rw [G.chord_inv]; apply le_trans (add_le_add (G.chord_triangle _ _|>.trans (add_le_add (he _) (hp i))) (he _)); apply le_of_eq; ring

def expense (G:Gauge) (a b : ℝ) := 4*a*(b*Blaze.royalty G)*(Blaze.royalty G)+ (b*Blaze.royalty G+4*a*(b*Blaze.royalty G))
lemma modeBasis {X:Type}[NormedAddCommGroup X] [NormedSpace ℝ X] {U:X→ Config G c} (x:X) (h:Mode U x j d) (ha: (c.val:ℝ)≤ a) (u:G.El) : Mode (fun y=>chainT u (U y)) x j (expense G a d):= by
  have hu : 0≤ d:=h.pos; have hx:= royalty_ge G; have hp : 0 ≤ a := (Nat.cast_nonneg _).trans ha
  apply Blaze.soak (U:=fun i=> root (U i)) _
  refine ⟨by unfold expense; positivity,fun i=>?_⟩
  let w (i:Site c) y:= carrier 0 (U y) i; have hK (i:Site c): Brush j r (4*a*(d*r)) (G.mat ∘ w i) x:= (tour _ (0:Site c) h.pos h.atLink).climb le_rfl (mul_le_mul_of_nonneg_right (anchorFee ha _) (by positivity))
  unfold root Lattice.gauge; simp only [G.mat_mul,mul_assoc]; apply Blaze.links (f:=w i.1) (hK _) _ (Blaze.royalty G) (max_le hx le_rfl)
  exact Blaze.links (f:=fun y=> U y i) (h.atLink _) (Blaze.reverse (hK _)) (Blaze.royalty G) (max_le hx le_rfl)

def shine (j:ℕ) (k v:ℝ) := (1+j.factorial*k)*((1+v)*1)
lemma mode_map {K:ℝ} (hs : Uniform.shade G * d ≤ 1) (h: ∀ i:G.Color, ‖i‖ ≤ 1 → Brush j K 1 (fun y => G.mat (G.lieExp y)) i) (x:E) (hx: ‖x‖ < d) (hd:d≤1) :
    Mode (fun k:E=> actual k) x j (shine j K (Uniform.shade G)):= by
  let f (v:E) (i:Bond c):= tint G _ v (pole i); have hv : Brush j (Uniform.shade G) 1 f x:= by
    refine Brush.fold zero_le_one (Uniform.shade_pos _).le (fun i=> ?_)
    let L: Positions (Uniform.Primary c G)→L[ℝ] G.Color:= ContinuousLinearMap.proj (pole i) ∘L (tint G _).toContinuousLinearMap
    have he (y:E) : ‖L y‖ ≤ Uniform.shade G * ‖y‖:= (norm_le_pi_norm (tint G _ y) (pole i)).trans (tint_le _)
    exact linearB L ((he x).trans (mul_le_of_le_one_right (Uniform.shade_pos _).le (hx.le.trans hd))) (ContinuousLinearMap.opNorm_le_bound _ (by have hu:= Uniform.shade_pos G; positivity) (by simpa only [mul_one] using! he)) zero_le_one
  exact fromLogL _ hv 1 zero_lt_one h (fun i => (norm_le_pi_norm (tint G _ x) (pole i)).trans ((Uniform.tint_le _).trans ((mul_le_mul_of_nonneg_left hx.le (Uniform.shade_pos _).le).trans hs))) 1
lemma lit_exp (i : Bond c) {K Q : ℝ} (u₀ : E) (hr : ∀ i:G.Color, ‖i‖ ≤ d₀→ G.chord (G.lieExp i) ≤ K*‖i‖)
    (hk:0 ≤ K) (hQ:Uniform.shade G * ‖u₀‖≤ Q) (he:Q≤d₀): G.chord (actual u₀ i) ≤ K*Q:= by
  unfold Boulevard.actual; rw [Work.F03.represent_link]
  have hc:= (norm_le_pi_norm (tint G _ u₀) (pole i)).trans ((tint_le u₀).trans hQ)
  exact (hr _ (hc.trans he)).trans (mul_le_mul_of_nonneg_left hc hk)

section map
variable {e s s' z d' b J k ℓ₁ ℓ₂ : ℝ} {χ:Chi}
variable (Q : Frond.Suitable G j J d' 1) (R : Reliable G k b) (x:Positions (Uniform.Primary c G)) (u:G.El)
include R

lemma mapped (hs:∀ᶠ y:E in 𝓝 x,∀ i:Bond c,G.chord (chainT u (actual y) i) ≤ k) :
    actual ∘ convertLinks χ k u ∘ actual =ᶠ[𝓝 x] fun y:E=> chainT u (actual y):= by
  filter_upwards [hs] with y hy; ext1 i
  simp only [Function.comp_apply]; change represent (tint G _ ((tint G _).symm _)) i=_; rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [Work.F03.represent_link]; change G.lieExp (SliceRows.toLog (fun i=> cutLog χ k (chainT u (actual y) i)) (pole i))= _; rw [SliceRows.at_pole]; rw [R.kept χ _ (hy i)]; exact R.right _ ((hy i).trans (by have hx:=R.down; linarith))

include Q
open Metric in
lemma germPrice (h:Mode (fun y:E=> chainT u (actual y)) x j a) (hp:∀ i:Bond c, ‖G.mat (chainT u (actual x) i)-1‖ ≤ d')
    (hs:∀ᶠ y:E in 𝓝 x,∀ i:Bond c,G.chord (chainT u (actual y) i) ≤ k):
      Brush j (j.factorial*J) ((1+r)*a) (convertLinks χ k u ∘ actual) x:= by
  have ht:= (Frond.ep h Q hp).1
  let q:=(tint G (Exterior.Body 1 c)).symm; have he : ‖q.toContinuousLinearMap‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=> by rw [one_mul]; exact Uniform.tint_inv_le _)
  have hf:= ht.report q.toContinuousLinearMap he; rw [one_mul] at hf
  apply hf.shimmy; filter_upwards [hs] with y hy; apply congr_arg q; funext i; apply R.kept; exact hy _
omit R Q
include R
lemma shortKey (s:ℝ) (he:s≤k) (h:∀ i,G.chord (chainT u (actual x) i)≤ s): ‖convertLinks χ k u (actual x)‖ ≤ b*s:= by
  have hs:0 ≤ s:= (chord_nonneg G _).trans (h ((0,0):Bond c)); unfold convertLinks; apply (tint_inv_le _).trans; refine (pi_norm_le_iff_of_nonneg (mul_nonneg R.price.le hs)).2 (fun i=>?_)
  let e := Work.E03.poleEquiv c; obtain ⟨i,rfl⟩:=e.surjective i
  let w:= chainT u (actual x) i
  have hv:= h i; rw [show e i=pole i from rfl, SliceRows.at_pole]
  change ‖cutLog χ k w‖≤_; rw [R.kept χ w (hv.trans he)]; apply (R.cap w (hv.trans (by linarith only [he,R.down]))).trans (mul_le_mul_of_nonneg_left hv R.price.le)
end map
end YM.LocalLTE.Frame
