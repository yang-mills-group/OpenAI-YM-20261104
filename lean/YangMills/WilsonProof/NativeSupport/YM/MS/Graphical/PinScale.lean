import YM.MS.Graphical.PinScale
import YM.MS.Graphical.MeshDensity

/-!
# Costs for the actual time-dependent multi-pin vertices at finite IR length

Paid in *log* times t bounded above (i.e. scale lengths exp(t) bounded above).
`Pays R f u` uses the standard row seminorm bounds in `fell`, on the *rescaled*
fiber (includes field degree factor and momentum argument scaling in `plow`).
Constants/seminorm bounds are uniform through such times for the indicated rate
and uniformly in regulator parameter `z` on compacts in the disc of radius R.
No IR removal is attempted at this stage.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff
variable {I E J : Type} {U : Set ℂ} {p t v a b c R : ℝ} {m n : ℕ} {G : Gauge} {k j : I→ ℝ} {Y Z : I→ℂ}


/-- In scaled momenta. Scaling factors included. -/
private def small (t : ℝ) (F : Mob G) := plow 0 (-t) F

def Pays (R : ℝ) (f : Schedule G) (u : ℝ) := ∀ (I:Type) (v : I → ℝ) (Z : I→ℂ) (B : ℝ),
  (∀ i, v i ≤ B) → ∀ K, IsCompact K → K ⊆ disc R → (∀ i,Z i ∈ K) →
    fell 0 (fun i=> Real.exp (u*v i)) fun i=> plow 0 (-v i) (f (v i) (Z i))

/-- Upper bound by *some* exponential in logarithmic time (not necessarily
decaying as t → -∞). -/
abbrev Subponential (R : ℝ) (f : Schedule G) := ∃ b, Pays R f b
/-- Bounds for *every* exponential rate: rapid decrease toward the UV. -/
abbrev InPins (R : ℝ) (f : Schedule G) := ∀ b, Pays R f b

lemma exp_rate_bound (ha : p≤a) (hp : a≤t) (hb : ∀ i,v*k i ≤ b) (i : I) :
    Real.exp (a*(v*k i)) ≤ Real.exp ((t-p)*max 0 b)*Real.exp (p*(v*k i)):= by
  rw [← Real.exp_add]; apply Real.exp_monotone; specialize hb i
  let B:=max 0 b
  have h0:b≤B:=le_max_right ..; have ht:0≤B:=le_max_left ..; change _≤_*B+_
  nlinarith

lemma rate_uniform (h : IsCompact U) (hc : ∀ i,Z i∈ U) (F : ℂ→ℝ) (hx : ContinuousOn F U) :
    scaleC 0 1 fun i=> F (Z i) := by
  obtain ⟨C,hC⟩:= (h.image_of_continuousOn hx).bddAbove
  refine ⟨max C 1,lt_max_of_lt_right zero_lt_one,0,fun i _ _=>?_⟩
  simpa only [Pi.one_apply,pow_zero,mul_one] using (hC (mem_image_of_mem _ (hc i))).trans (le_max_left C 1)

lemma rate_expense (hK : ∀ i,k i≤ b) (hc : ∀ i,p≤(Z i).re) (hY : ∀ i, (Z i).re ≤ t) :
    scaleC 0 (fun i=>exp (p*k i)) (fun i=> ‖amount (Z i) (k i)‖) := by
  refine ⟨exp ((t-p)*max 0 b),exp_pos _,0,fun i _ _=>?_⟩
  obtain hv:= exp_rate_bound (v:=1) (k:=k) (hc i) (hY i) (by simpa using hK) i
  simp only [amount,Complex.norm_exp,Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.ofReal_re, pow_zero,mul_one]; rw [mul_comm (k i)]; simpa only [one_mul] using hv

section comparison
variable {f : I → Mob G} {B : ℝ} {p q : I→ℝ}
lemma flatRate (hp : fell 0 p f) (C : ℝ) (hC : 0<C) (h : ∀ i, p i ≤ C*q i) : fell 0 q f :=
  fun m E _ _ _ w=> (hp m E w).raise ⟨C,hC,0,fun i _ _=> by simpa only [pow_zero,mul_one] using h i⟩

lemma downRate (hv : ∀ i, k i ≤ B) (hp : fell 0 (fun i=>exp (a*k i)) f) (h : c≤a) :
    fell 0 (fun i=>exp (c*k i)) f :=
  flatRate hp _ (exp_pos ((a-c)*max 0 B)) (fun i=> by
    simpa only [one_mul] using exp_rate_bound h (le_refl _) (k:=k) (v:=1) (b:=B) (by simpa using hv) i)
end comparison

variable {F H : Schedule G} {w : ℝ} {U : Rip G}

lemma Pays.more (hf : Pays R F v) (ht : t ≤ v) : Pays R F t :=
  fun I k l B hv U h hx hk=> downRate hv (hf I k l B hv U h hx hk) ht

-- scale algebra
lemma bring_scale (t : ℝ) (u : Tone.QP) (F : Mob G) :
    plow 0 t (bring u F)= bring (exp t • u) (plow 0 t F):= by
  ext m l; simp only [plow,bring, phase_smul, net_sr]; ring

lemma shuffle_scale (t : ℝ) (F H : Mob G) :
    plow 0 t (shuffleRows F H)=shuffleRows (plow 0 t F) (plow 0 t H) := by
  funext n l; unfold shuffleRows; rw [plow,scattered,scattered,scatter_sr]
  let Q:= allocate (field Landau.parity) l (R:=ℂ)
  change amount _ t • Q _ = _; rw [← map_smul]; refine scatter_congr _ _ _ _ (fun a b he=>?_)
  simp only [plow,Pi.smul_apply,smul_eq_mul,zero_add,← price_mag_split he,Int.cast_add,amount_add]
  ring

lemma close_scale (f : Mob G) (hf : kPrice f) (y t : ℝ) (z : ℂ) :
    plow 0 (-t) (radialClose (halfD t) z y f)= amount (-2*z) t • radialClose (halfD 0) z y (plow 0 (-t) f) := by
  let F:= plow 0 (-t) f; let U:=A0 G 0
  have he : plow 0 t F=f:= by unfold F; rw [snow,add_neg_cancel,posing]
  obtain h:=air_ocean (powder hf 0 (-t)) (c_bo 0 (G:=G) (b:=false)).price z 4 0 t
  change ocean z (pulse _ _ U) (plow 0 t F) = _ at h; unfold U at h
  rw [pA, he,show (4:ℂ)+0-4-2*z=0+(-2*z) from by ring, Alps.shift] at h
  simp_rw [halfD_eq,radialClose_eq_ocean,h,← cert, map_smul,cert,snow, neg_add_cancel,posing, smul_comm (tenorK z y)]

lemma wick_scale (u : Tone.QP) (f g : Mob G) (hf : kPrice f) (hp : kPrice g) (t y : ℝ) (z : ℂ) :
    plow 0 (-t) (wickJoin u (halfD t) z y f g)= amount (-2*z) t •
        wickJoin (exp (-t) • u) (halfD 0) z y (plow 0 (-t) f) (plow 0 (-t) g):= by
  obtain he : kPrice (bring u f):= bring_cost _ hf ⟨_,fun _=>le_rfl⟩
  have ht : kPrice (shuffleRows (bring u f) g):= by convert shuffle_cost he hp using 1; ext; simp
  unfold wickJoin; rw [← cert,map_sub,map_sub]; simp only [cert, shuffle_scale,close_scale _ ht y t z, close_scale _ he y t z, close_scale _ hp y t z,bring_scale];
  funext n; simp only [shuffleRows, Pi.smul_apply, Pi.sub_apply,map_smul,LinearMap.smul_apply,smul_sub]


namespace Pays
lemma close (F : Schedule G) (hf : Pays R F w) (hU : disc R ⊆ Town) (hR : R≤1) (y : ℝ)
    (hp : ∀ t:ℝ, ∀ z∈disc R, Form0 false (F t z)) :
    Pays R (fun t z=> radialClose (halfD t) z y (F t z)) (w-2) := by
  intro I t Z B hv K HK hK h
  have he(i:I): Form0 false (F (t i) (Z i)):= hp _ _ (hK (h i))
  simp_rw [show ∀ i, plow 0 (-t i) (radialClose (halfD (t i)) (Z i) y _)=_ from fun i:I=> close_scale _ (he i).price y (t i) (Z i) ]
  let f i := plow 0 (-t i) (F (t i) (Z i))
  have ht (i:I): Form0 false (f i):= fseed (he i) ..
  let d(i:I):= exp (w*t i)
  obtain h0 : fell 0 d f:= hf I t Z B hv K HK hK h
  have hc(i:I) : |(Z i).re| ≤ 1:= (Complex.abs_re_le_norm _)|>.trans ((mem_ball_zero_iff.mp (hK (h i))).le.trans hR)
  let U := A0 G 0
  have hX : fell 0 d (fun i=>ocean (Z i) U (f i)) := by
    obtain h := regular_fin (Z:=Z) (n:=3) (fun j:ℕ=> rate_uniform HK h (fun z:ℂ=> ‖2*(z-j)‖) (show ContinuousOn _ _ from Continuous.continuousOn (by fun_prop))) h0
      (transport (c_bo 0 (G:=G) (b:=false)).price) (fun i=> hU (hK (h i))) (by intro i; have hx:=abs_le.mp (hc i); norm_num; linarith [hx.2])
      (fun i=>(ht i).token) (fun _=>(c_bo 0 (b:=false) (G:=G)).token) (fun _=>zero_le_one)
    convert h using 1; ext; simp
  have ht : fell 0 d (fun i=>radialClose (halfD 0) (Z i) y (f i)) := by
    simp_rw [halfD_eq,radialClose_eq_ocean]; convert fall_scale hX (rate_uniform HK h (fun z=>‖tenorK z y‖) (ContinuousOn.norm (f:=fun z=>tenorK z y)
        (fun z hz=> (tenor_hol y _ (hU (hK hz))).continuousAt.continuousWithinAt))) using 1; ext; simp
  have hy : scaleC 0 (fun i=>exp (-2*t i)) (fun i=> ‖amount (-2*Z i) (t i)‖) := by
    apply rate_expense hv (t:= (2:ℝ)) (Z:=fun i=>-2*Z i);
    all_goals intro i; obtain ⟨hj,h⟩:= abs_le.mp (hc i); norm_num; linarith
  convert fall_scale ht hy using 1; funext i; unfold d; rw [← Real.exp_add]; congr 1; ring

lemma attach_scale (s : ℝ) (F H : Mob G) :
    plow 0 (-s) (bridging s F H) = amount 4 s •
       bridging 0 (plow 0 (-s) F) (plow 0 (-s) H) := by
  have he (X:Mob G) : plow 0 s (plow 0 (-s) X)=X:= by rw [snow,add_neg_cancel,posing]
  obtain hp:= air_tree (F:=plow 0 (-s) F) (H:=plow 0 (-s) H) 4 0 0 s (reverse_a G 0)
  simp only [pA, he, add_zero] at hp; simp only [bridging_eq,hp]
  rw [show plow (4:ℂ) s _ = amount (4:ℂ) s • plow 0 s (arbor (A0 G 0) _ _) from ?_, ←cert,map_smul,cert, snow, neg_add_cancel,posing];
  simp_rw [← Alps.shift,zero_add]

lemma attach (hf : Pays R F a) (hg : Pays R H b) :
    Pays R (fun t z=> bridging t (F t z) (H t z)) (a+b+4) := by
  intro I t Z B hv K HK hK h
  simp_rw [attach_scale];
  have he:=for_tree (r:=1) (hf I t Z B hv K HK hK h) (hg I t Z B hv K HK hK h) (u:=fun _=> A0 G 0)
            (fun i j l=> railto (Rock.transport (c_bo 0 (G:=G) (b:=false)).price i j l)) (fun _=>zero_le_one)
  simp_rw [bridging_eq]; convert fall_scale he (U:=fun i=> amount 4 (t i)) (rate_expense hv (Z:=fun _=>4)
       (p:= (4:ℝ)) (t:=(4:ℝ)) (by norm_num [← Complex.ofReal_ofNat]) (by norm_num [← Complex.ofReal_ofNat])) using 1
  ext i; simp only [Pi.one_apply,one_mul,← Real.exp_add]; congr 1; ring

lemma joins (hf : Pays R F a) (hg : Pays R H b) (hU : disc R ⊆ Town)
    (hR : R≤1) (y : ℝ) (hp : ∀ t:ℝ, ∀ z∈disc R, Form0 false (F t z))
    (hh : ∀ t:ℝ, ∀ z∈disc R, Form0 false (H t z)) (x : Tone.QP) (hx : x≠0) :
    InPins R fun t z=> wickJoin x (halfD t) z y (F t z) (H t z) := by
  intro c I t Z B hv K HK hK h
  have hm(i:I): Form0 false (F (t i) (Z i)):= hp _ _ (hK (h i))
  have hn(i:I): Form0 false (H (t i) (Z i)):= hh _ _ (hK (h i))
  obtain ⟨k,hk⟩:= exists_nat_ge (c-(a+b-2))
  let A := a+b+(k:ℝ);
  let r :=fun i:I=> exp (t i-B); let X i p:= plow (G:=G) 0 (-t i) p; let Y:= exp (-B) • x
  let f i:= X i (F (t i) (Z i)); let g i:= X i (H (t i) (Z i))
  have hy:Y≠0:= smul_ne_zero (exp_pos _).ne' hx
  have ht:=c_bo 0 (G:=G) (b:=false)
  obtain hW:= falloff_join (hf I t Z B hv K HK hK h) (hg I t Z B hv K HK hK h) (Rock.transport ht.price)
       (fun _=>zero_le_one) (s:=r) (fun i=>exp_pos _) (fun i=> Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hv i))) hy HK (Subset.trans hK hU) h
       (fun i=> (fseed (hm i) ..).token) (fun i=> (fseed (hn i) ..).token) (fun i=> ht.token)
       (fun i=>reverse_a G 0) (fun i=> cl_a G 0) y k
  let Gg i:= wickJoin (exp (-t i) • x) (A0 G 0) (Z i) y (f i) (g i)
  have hd : fell 0 (fun i=> exp (A*t i)) Gg := by
    have hp : ∀ i, (r i)⁻¹ • Y=exp (-t i) • x := by
      intro i; unfold r Y; rw [smul_smul, ← Real.exp_neg,← Real.exp_add,show -(t i-B)+ -B= -t i from by ring]
    simp_rw [hp] at hW
    refine flatRate hW (exp (-k*B)) (exp_pos _) ?_
    intro i; unfold r; rw [Pi.one_apply,one_mul, ← Real.exp_nat_mul]; simp_rw [← Real.exp_add]
    unfold A; apply le_of_eq; congr 1; ring
  simp_rw [wick_scale x _ _ (hm _).price (hn _).price, halfD_eq];
  apply downRate (a:=A-2) hv _ (by unfold A; linarith)
  have hc(i:I) : |(Z i).re| ≤ 1:= (Complex.abs_re_le_norm _)|>.trans ((mem_ball_zero_iff.mp (hK (h i))).le.trans hR)
  have hy : scaleC 0 (fun i=>exp (-2*t i)) (fun i=> ‖amount (-2*Z i) (t i)‖) := by
    apply rate_expense hv (t:= (2:ℝ)) (Z:=fun i=>-2*Z i);
    all_goals intro i; obtain ⟨hj,h⟩:= abs_le.mp (hc i); norm_num; linarith
  convert fall_scale hd hy using 1; funext i; rw [← Real.exp_add]; congr 1; ring
end Pays
end YM.MS.Graphical
