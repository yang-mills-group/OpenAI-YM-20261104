import YM.XSpace.Compat.Tile
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Mesh-integration helpers recovered from the hash-pinned Oct15 source.
The original covariance/symbol/Weight definitions retain their baseline identity.
New helper declarations live only in this compatibility namespace. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent Exterior Matrix Precision
open scoped Topology ContDiff BigOperators InnerProductSpace Real ComplexConjugate
variable {ι : Type*} {n : Side} {α Ω η : ℝ}
variable {f : ι → E4 → ℂ}
lemma meal_ok {f : E4 → ℂ} (hf : Integrable f) (x : E4) :
    Integrable (fun p => song x p * f p) := by
  have H : Continuous (song x) := (song_smooth x (n := (0:ℕ))).continuous
  exact hf.norm.mono' (H.aestronglyMeasurable.mul hf.1)
    (Eventually.of_forall fun p => by rw [norm_mul, song_fee, one_mul])
lemma zero_error (h : Weight whole 0 f) (hz : ∀ a, f a 0=0) : ∃ C:ℝ, 0≤C ∧ ∀ i,∀ n,∀ p:E4,p≠0→∀ x:E4,
    ‖song x (pick n p)*f i (pick n p)-song x p*f i p‖≤ C*leap n*(1+‖x‖)*(1+‖p‖⁻¹) := by
  obtain ⟨A,hA,H⟩ := h.quotes 0; obtain ⟨B,hB,K⟩:= h.quotes 1; let L := max A B
  have hL : 0≤L:= hA.trans (le_max_left ..)
  have he (i) (p:E4) : ‖f i p‖≤L := by
    by_cases hp:p=0; rw [hp,hz,norm_zero]; exact hL
    exact (show ‖f i p‖≤A by simpa using H i p hp).trans (le_max_left ..)
  refine ⟨16*L,by positivity,fun i n p hp x => ?_⟩
  let r:=‖p‖; let b:=pick n p; let t:=leap n; have ht : 0<t:=leap_pos _; have hr : 0<r:=norm_pos_iff.mpr hp
  have hd : ‖b-p‖≤2*t := pick_near n p
  have hb : ‖song x b-song x p‖≤‖x‖*(2*t) := by
    have hu : ‖song x b-song x p‖≤‖x‖*‖b-p‖ := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _=> (song_gradient x z).differentiableAt)
      (fun z _=> by rw [← norm_iteratedFDeriv_one]; simpa using song_quotes 1 x z) (convex_univ ..) (mem_univ _) (mem_univ _)
    exact hu.trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
  have hs : ‖f i b-f i p‖≤ 8*L*t * r⁻¹ := by
    by_cases ha:r≤4*t
    · apply ((norm_sub_le ..).trans (add_le_add (he i b) (he i p))).trans; rw [← div_eq_mul_inv, le_div_iff₀ hr]; linarith [mul_le_mul_of_nonneg_left ha hL]
    let s:=closedBall p (r/2)
    have hh (z:E4) (hz:z∈s) : r/2≤‖z‖ := by
      have hm := norm_sub_norm_le p z
      have hh := mem_closedBall.mp hz
      rw [dist_comm,dist_eq_norm] at hh
      change ‖p-z‖≤ ‖p‖/2 at hh
      unfold r
      linarith
    have hu : s⊆whole.look := fun z hz=> norm_pos_iff.mp ((half_pos hr).trans_le (hh z hz))
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x hx=> ((h.smooth i).contDiffAt (whole.ok.mem_nhds (hu hx))).differentiableAt (by simp))
      (fun z hz=> show ‖fderiv ℝ (f i) z‖≤ L*(r/2)⁻¹ from by specialize K i z (hu hz); rw [norm_iteratedFDeriv_one] at K; simp only [Nat.cast_one,zero_sub,_root_.zpow_neg,zpow_one] at K; apply K.trans; gcongr; exacts [le_max_right .., hh z hz])
      (convex_closedBall p (r/2)) (mem_closedBall_self (by positivity)) (show b∈s by rw [show s=closedBall p (r/2) from rfl,mem_closedBall,dist_eq_norm]; linarith)
    apply he.trans; apply le_trans (mul_le_mul_of_nonneg_left hd (by positivity)); rw [inv_div]; have hb : 0≤L*t*r⁻¹ := by positivity
    ring_nf; linarith
  change ‖song x b*f i b-song x p*f i p‖ ≤ 16*L*t*(1+‖x‖)*(1+r⁻¹)
  rw [show song x b*f i b-song x p*f i p=(song x b-song x p)*f i b+song x p*(f i b-f i p) by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul,song_fee,one_mul]
  apply le_trans (add_le_add (mul_le_mul hb (he i b) (norm_nonneg _) (by positivity)) hs); rw [← sub_nonneg]; ring_nf; positivity

def ceiling := 2*earth+4*Real.pi +1
def food (p:E4) := 1+‖p‖⁻¹
def station := (ball (0:E4) ceiling).indicator food
lemma stomach : Integrable station := by
  have he : IntegrableOn (fun p:E4=>‖p‖⁻¹) (ball (0:E4) ceiling) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp [E4,Axis]) (α:= (↑(1:ℕ):ℝ)) (by norm_num [E4,YM.Axis]) (C:=1) _ (measurable_norm.inv.aestronglyMeasurable)
    apply Eventually.of_forall
    intro p; rw [Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]; simp
  exact ((integrableOn_const measure_ball_lt_top.ne).add he).integrable_indicator measurableSet_ball
lemma station_nonneg (p:E4) : 0≤station p := indicator_nonneg (fun p _=>by unfold food; positivity) _
lemma door_shut {p:E4} (hp : 2*earth < ‖p‖) : house p=0 := by
  refine house_off p fun h => ?_
  have hf : p≠0 := norm_pos_iff.mp (lt_trans (by positivity [earth_pos]) hp)
  have he:=search_short p (show p∈search from ⟨fun i => (h i).trans_lt fearless.2,hf⟩)
  linarith
lemma mesh_quote (f : ι→E4→ℂ) (g : ι→E4→ℂ) (hh : ∀ i p, g i p= house p*f i p) (h : Weight whole 0 g) (hz : ∀ a, g a 0=0) (he : ∀ i, Integrable (g i)) : ∃ C:ℝ, 0≤C ∧ ∀ i,∀ n,∀ x:E4,
    ‖(leap n)^4 • (∑ a:Site n×St,song x (lit n (pav n a))*g i (lit n (pav n a))) - feed (g i) x‖ ≤ C*leap n*(1+‖x‖) := by
  obtain ⟨C,hC,H⟩:=zero_error h hz; refine ⟨C*∫ x, station x,mul_nonneg hC (integral_nonneg station_nonneg),fun i n x => ?_⟩
  let w (p:E4) := song x p*g i p
  have hw p : house p*(song x p*f i p)=w p := by unfold w; rw [hh]; ring
  obtain ⟨hf,hf'⟩ := clip_pay n (fun p=> song x p*f i p); simp_rw [hw] at hf hf'
  change ‖((leap n)^4) • (∑ _, w _) - ∫ p, w p‖ ≤ _; rw [← hf',← integral_sub hf (meal_ok (he i) x)]
  let t:= C*leap n*(1+‖x‖); have ht : 0≤t:= by unfold t; positivity [leap_pos n]
  apply (norm_integral_le_integral_norm ..).trans; apply le_trans (integral_mono_ae ((hf.sub (meal_ok (he i) x)).norm) (stomach.const_mul t) ?_); swap
  · have he : ∀ᵐ x:E4,x≠0 := mem_ae_iff.mpr (by change volume ({x:E4 | x≠0}ᶜ)=0; simp)
    filter_upwards [he] with p hp; by_cases hv : p∈ball (0:E4) ceiling
    · change ‖w (pick n p)-w p‖ ≤ _; exact (H i n p hp x).trans_eq (by simp [station,food,t,hv])
    have hT := not_lt.mp (mt mem_ball_zero_iff.mpr hv); unfold ceiling at hT
    have hp := door_shut (p:=p) (by linarith [Real.pi_pos]); have hy : house (pick n p)=0 := by
      have he : leap n ≤ 2*Real.pi := div_le_self (by positivity) (by exact_mod_cast (show 1≤n.val from n.property))
      have hd := norm_sub_norm_le p (pick n p); rw [norm_sub_rev] at hd; apply door_shut; linarith [pick_near n p]
    change ‖w _ - w _‖ ≤ _; simp [w,hh i _,hp,hy,hv,station]
  rw [integral_const_mul]; unfold t; ring_nf; exact le_refl _
end YM.XSpace.Compat.KP
end
