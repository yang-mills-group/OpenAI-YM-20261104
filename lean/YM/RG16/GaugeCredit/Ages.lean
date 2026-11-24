import YM.RG16.GaugeCredit.Curve

/-!
# On the soft return window: pay actual step scales, select short and long stops

Use calendar Λ. Expose inner assumptions via general age hypotheses (allowing
any priced layout in that window, not choosing a phase or shifting origins).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Guarding
open Set Filter Function Lattice Wilson RG Source MergeProof OPE Pert Literal
open Pert.Asymptotics Trace.Physical.GermGraph
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G:Gauge}(C:Family G)(H:C.Makes)(hG:G.Simple)
set_option quotPrecheck false
local notation "S" => C.S.scale
local notation "P" => C.path.levels
local notation "L" => factor C
local notation "B" => C.path.levels.clock.hatBeta
local notation "Λ" => Lambda C.path.levels
local notation "g" => regulatorRun C
local notation "M" => coin C

def gap (i j:ℕ) := C.S.scale j-C.S.scale i

structure Short (j k:ℕ)(a:ℝ) : Prop where
   hk : j≤ k
   verge : gap C j k ≤ a*(Λ k)
variable {i j k u p N:ℕ} {a b c:ℝ}
lemma Short.latest (S₀:Short C j k a) (he:j ≤ i)(hp:i ≤ k) : Short C i k a:=
   ⟨hp,le_trans (sub_le_sub_left ((scale_mono _).monotone he) _) S₀.verge⟩
lemma bounds_num (hi : i ≤ k) : ((k:ℝ)-i)*Real.log 3 ≤ gap C i k:=by
   induction k,hi using Nat.le_induction with
   | base=>simpa only [sub_self,zero_mul,gap] using (le_refl (0:ℝ))
   | succ k hi ih=>
     have hv: Real.log 3 ≤ Real.log (C.S.block k).val:= Real.log_le_log (by norm_num) (by exact_mod_cast C.S.block_large k)
     unfold gap at *; rw [Schedule.scale_succ,Nat.cast_add_one]; linarith only [ih,hv]
lemma steps (S₀:Short C j k a) (he:j≤ i)(hp:i≤k): ((k:ℝ)-i) ≤ a/Real.log 3*(Λ k):= by
   rw [div_mul_eq_mul_div]; exact (le_div_iff₀ (Real.log_pos (by norm_num:(1:ℝ)<3))).mpr ((bounds_num C hp).trans (Short.latest C S₀ he hp).verge)
lemma tGap (i j:ℕ) (x:ℝ): hike C i j x=Real.exp (x*(C.S.scale j-C.S.scale i)) := by
   have hi:= C.S.a_pos i; have hj:= C.S.a_pos j
   unfold hike Schedule.scale
   rw [Real.rpow_def_of_pos (div_pos hi hj), Real.log_div hi.ne' hj.ne',Real.log_inv,Real.log_inv]
   ring_nf
lemma Short.clamps (ha:0≤a)(h:Short C j k b)(hi:j≤ i)(hp:i≤k) : hike C i k a ≤ coin C (-(2*a*b)) k := by
   rw [tGap,coin]; apply Real.exp_le_exp.mpr; have hE:=Short.latest C h hi hp|>.verge; exact le_trans (mul_le_mul_of_nonneg_left (show S k-S i ≤ b*Λ k from hE) ha) (le_of_eq (by ring))
-- use eventual v L^gamma for fine growth, base older tail exponent θ=rate/2. require LONG tail dominated by spent older spacing within short window. norms ft~k. prepare inequality.
lemma expenses {δ θ s:ℝ}(h : Short C j k a) (he:b*(Λ k) ≤ gap C j i)
   (hδ:0≤δ)(ht:0≤θ)(hS:a*θ-b*δ ≤ -s/2) :
   hike C j k θ * hike C i j δ ≤ coin C s k:= by
   rw [tGap,tGap,← Real.exp_add]; apply Real.exp_le_exp.mpr
   have hv : θ*gap C j k ≤ θ*(a*(Λ k)):= mul_le_mul_of_nonneg_left h.verge ht
   have hx := mul_le_mul_of_nonneg_left he hδ
   have hw:= mul_le_mul_of_nonneg_right hS (lambda_pos C k).le
   unfold gap at hv hx; linarith only [hv,hx,hw]

-- Window finite period and powers
lemma hat_charged (i:ℕ) : B i= Real.exp ((Λ i)-2) := by
   have hi:= zero_lt_one.trans ((P).fits.delayed i)
   rw [Lambda,add_sub_cancel_left _, Real.exp_log hi]
include hG
lemma latitude : RateIs atTop Λ B 1 := by
   refine RateIs.exp' (f:=fun i=>Λ i-2) ?_|>.congr (Eventually.of_forall fun i=>(hat_charged C i).symm)
   have hi: Tendsto (fun i=>2/Λ i) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (lambda_leads C hG)
   have h₁: Tendsto (fun i : ℕ=> 1- 2/Λ i) atTop (𝓝 1) := by simpa only [sub_zero] using! tendsto_const_nhds.sub hi
   exact h₁.congr (fun i=> by rw [sub_div,div_self (lambda_pos C i).ne'])

lemma sugar (a:ℝ) : ∀ᶠ k in atTop,∀ i:ℕ,Short C i k a → B k/2 ≤ B i:= by
   have he: RateLE atTop Λ (fun i=> 2*G.slopeConstant*a*Λ i) 0:= by
       simpa only [zero_add] using! (RateLE.const _ (lambda_leads C hG)).mul ((blue C hG).pays (lambda_leads C hG))
   filter_upwards [allocate C hG zero_lt_one he (latitude C hG)] with k hk i hi
   have hs := mul_le_mul_of_nonneg_left hi.verge (Gauge.slopeConstant_pos hG).le
   change G.slopeConstant*(S k-S i) ≤ _ at hs; change B k/2 ≤ B i
   have hz : B i= B k-G.slopeConstant*(S k-S i):= by unfold Calendar.hatBeta; change _+_*(S i)=_+_*(S k)-_ ;ring
   rw [hz]; linarith only [hs,hk]
-- expose pack
structure Pack (j k:ℕ):Prop where
    hk : j ≤ k
    hat (i:ℕ): j≤ i → i≤ k → B k/2 ≤ B i ∧ B i ≤ B k
lemma taxed (a:ℝ) : ∀ᶠ k in atTop,∀ j:ℕ,Short C j k a → Pack C j k:= by
   filter_upwards [sugar C hG a] with k hk j hj
   exact ⟨hj.hk,fun i hi hp=> ⟨hk i (Short.latest C hj hi hp), add_le_add_right (mul_le_mul_of_nonneg_left ((scale_mono C.S).monotone hp) (Gauge.slopeConstant_pos hG).le) _⟩⟩
omit hG
lemma windowL (h : Pack C j k) (hi:j≤ i)(hp:i≤k) : Λ k - Λ i ≤ Real.log 2 := by
   have hx := (h.hat i hi hp).1; have he : B k ≤ 2*B i:= by linarith only [hx]
   have hw:=(P).fits.delayed i; have ht:=Real.log_le_log (zero_lt_one.trans ((P).fits.delayed k)) he; rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (zero_lt_one.trans hw).ne'] at ht
   unfold Lambda; linarith only [ht]
lemma window_tithe {x:ℝ}(hx:0≤x)(h:Pack C j k)(hi:j≤ i)(hp:i≤k) : coin C x i ≤ Real.exp (x/2*Real.log 2)*coin C x k:= by
   unfold coin; rw [←Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_left (windowL C h hi hp) hx])
include H in
lemma Pack.steed (hx: Pack C j k)(hi:j≤ i)(hp:i≤k)(hN:k≤N): (g N p k)/4 ≤ g N p i ∧ g N p i≤4*g N p k := by
   let v:= g N p i; let u:=g N p k
   let A:= C.path.β N p i; let b:= C.path.β N p k
   have hA:0<A:=Overlay.beta_positive H.wilson (hp.trans hN)
   have hb:0<b:=Overlay.beta_positive H.wilson hN
   have hv : 0<v:=g_pos H (hp.trans hN); have hu:0<u:=g_pos H hN
   have hp': v^2*A=1:=cashable C H (hp.trans hN)
   have hu' : u^2*b=1:=cashable C H hN
   have H₀ : B k/2≤ b ∧ b ≤ 2*B k:= (H.wilson.represents N p k hN).band
   have h₁ : B i/2 ≤ A ∧ A ≤ 2*B i := (H.wilson.represents N p i (hp.trans hN)).band
   obtain ⟨hX,hY⟩:=hx.hat i hi hp
   have hx: A≤8*b:=by linarith
   have hy:b≤8*A:=by linarith
   have hb' : u^2 ≤ 8*v^2:= le_of_mul_le_mul_right (a:=b) (by linarith only [mul_le_mul_of_nonneg_left hx (sq_nonneg v),hp',hu']) hb
   have hv' : v^2 ≤ 8*u^2:= le_of_mul_le_mul_right (a:=A) (by linarith only [mul_le_mul_of_nonneg_left hy (sq_nonneg u),hp',hu']) hA
   change u/4 ≤ v ∧ v≤4*u; constructor <;> nlinarith only [hv,hu,hb',hv']

variable (hpace: ∀ i,((C.S.block i).val:ℝ) ≤ Real.log (Lambda C.path.levels i))
section port
open scoped Classical
variable (K V₀:ℝ)(hK:0<K)(hV:0<V₀)
local notation "port₁" => port C K V₀ hK
include hG hpace hV
-- Choose Sgap k-port ≤ Λ (actual much shorter). This bound already buys normalization through replacement fits on our precision window. k uses literal geometry, not introducing continuum-meter corrections.
lemma port_near : ∀ᶠ i in atTop, Short C (port₁ i) i 1:=by
    let v(i):= port₁ i; let z(i):= Upper C K V₀ i*(Λ i)^ (2:ℕ)
    have hr : RateIs atTop Λ (z) 0:= by simpa only [z,Upper,mul_zero,add_zero] using!
       ((RateIs.const (lambda_leads C hG) hK).mul ((blue C hG).rpow (V₀+1))).mul ((blue C hG).power 2)
    filter_upwards [port_small C hG K V₀ hK hV, outer_bound C hG K V₀ hK hV hpace,
        allocate C hG zero_lt_one (hr.pays (lambda_leads C hG)) (RateIs.exp 1 (lambda_leads C hG))] with k hk hi hz
    have hx:Real.log (C.S.a (v k) / C.S.a k) ≤ 1*Λ k:= (Real.log_le_iff_le_exp (div_pos (C.S.a_pos _) (C.S.a_pos _))).mpr (hi.trans hz)
    rw [Real.log_div (C.S.a_pos _).ne' (C.S.a_pos _).ne'] at hx
    refine ⟨(Nat.le_succ _).trans hk.le,?_⟩; unfold gap Schedule.scale; rw [Real.log_inv,Real.log_inv];change - Real.log (C.S.a k) - -Real.log (C.S.a (v k)) ≤ _;linarith only [hx]
end port

section stopping
open scoped Classical
variable (x f j0:ℕ→ℝ)
private lemma exceed (x:ℝ) : ∃ i:ℕ, x < C.S.scale i:= (C.S.divergent.eventually_gt_atTop x).exists

def ebb (x:ℝ):ℕ := Nat.find (exceed C x)-1
-- true largest index with S≤x (except negative x padding)
lemma ebb_interval {x:ℝ}(hp:0 ≤ x) : S (ebb C x) ≤ x ∧ x < S (ebb C x+1):=by
    let i:=Nat.find (exceed C x)
    have he:x<S i:= Nat.find_spec (exceed C x)
    have hi:i ≠ 0:=by rintro h; rw [h,Schedule.scale_zero] at he; linarith only [hp,he]
    have hl : ebb C x=i-1:=rfl; rw [hl]
    refine ⟨le_of_not_gt (fun h=>?_), by rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hi)]⟩
    have hX:i ≤ i -1:= Nat.find_min' (exceed C x) h; omega
lemma ebb_live (h:Tendsto x atTop atTop) : Tendsto (fun i=>ebb C (x i)) atTop atTop:= by
    refine tendsto_atTop.mpr fun i=> ?_; filter_upwards [h.eventually_ge_atTop 0,h.eventually_ge_atTop (S i)] with k hk hp
    exact Nat.lt_succ_iff.mp ((scale_mono C.S).lt_iff_lt.mp (lt_of_le_of_lt hp (ebb_interval C hk).2))
-- k short stop referenced to actual metric

def shelfStep (a:ℝ)(i:ℕ):=ebb C (C.S.scale i-a*Lambda C.path.levels i)
-- b longer universal form

def longShelfStep (i:ℕ):=ebb C (C.S.scale i-(Lambda C.path.levels i)^2)
include hG
lemma tide (a:ℝ) : Tendsto (fun i=>C.S.scale i-a*Lambda C.path.levels i) atTop atTop:= by
   refine tendsto_atTop_mono' atTop ?_ (C.S.divergent.const_mul_atTop (by norm_num:(0:ℝ)<1/2))
   filter_upwards [(lambda_negligible C hG|>.const_mul a).eventually (gt_mem_nhds (show a*(0:ℝ)< 1/2 by rw [mul_zero]; norm_num)), C.S.divergent.eventually_gt_atTop 0] with i hi hz
   have hx : a* Λ i ≤ 1/2* C.S.scale i := (div_le_iff₀ hz).mp (by rw [mul_div_assoc]; exact hi.le)
   linarith only [hx]
lemma tide_sq : Tendsto (fun i=> S i - Λ i^ (2:ℕ)) atTop atTop:= by
   refine tendsto_atTop_mono' atTop ?_ (C.S.divergent.const_mul_atTop (by norm_num:(0:ℝ)<1/2))
   have he:= Gauge.slopeConstant_pos hG; let u:ℕ→ℝ:=fun i=> 2*G.slopeConstant*(Λ i)^ (2:ℕ)+(P).clock.bar; have hp : RateLE atTop Λ u 0:= by
       let ht:= blue C hG|>.pays (lambda_leads C hG)
       exact ((show RateLE atTop Λ (fun i:ℕ=>2*G.slopeConstant*(Λ i)^ (2:ℕ)) 0 from by simpa only [zero_add, mul_zero] using! (RateLE.const _ (lambda_leads C hG)).mul (RateLE.pow 2 ht (lambda_leads C hG))).add (RateLE.const _ (lambda_leads C hG)) (lambda_leads C hG))
   filter_upwards [allocate C hG zero_lt_one hp (latitude C hG)] with i hi
   change 2*_*_+(P).clock.bar ≤ (P).clock.bar+G.slopeConstant*S i at hi; change 1/2*S i ≤ S i -(Λ i)^2
   apply le_of_mul_le_mul_left (a:=G.slopeConstant) ?_ he; linarith only [hi]
lemma lives (a:ℝ) : Tendsto (shelfStep C a) atTop atTop:= ebb_live C (fun i=> S i-a*Λ i) (tide C hG a)
include hpace
lemma ran {a:ℝ}(ha:0<a) : ∀ᶠ i in atTop, Short C (shelfStep C a i) i (a+1) ∧ a*Λ i ≤ gap C (shelfStep C a i) i:= by
    filter_upwards [(tide C hG a).eventually_ge_atTop 0] with i hi
    let b:=shelfStep C a i
    have he:=ebb_interval C hi
    change S b ≤ S i-a*Λ i ∧ S i-a*Λ i < S (b+1) at he
    have ht: b < i:= (scale_mono C.S).lt_iff_lt.mp (lt_of_le_of_lt he.1 (sub_lt_self _ (mul_pos ha (lambda_pos C i))))
    rw [Schedule.scale_succ] at he
    have hx:= (Real.log_le_self (show 0≤L b from (zero_lt_one.trans (factor_positive C b)).le)).trans ((hpace b).trans ((Real.log_le_self (lambda_pos C b).le).trans ((lambda_mono C hG).monotone ht.le)))
    refine ⟨⟨ht.le,?_⟩,?_⟩ <;> (try unfold factor at hx) <;> (first|change S i-S b ≤ _ | change _ ≤ S i-S b ) <;>linarith

-- longer stop at b is in living range and coarser than shelf k --- for all short captures. Provide ad-hoc port or otherwise.
lemma twice (b:ℕ→ℕ) (hb:Tendsto b atTop atTop) (he:∀ᶠ i in atTop, Short C (b i) i 1) {a:ℝ}(ha:1<a) :
    ∀ᶠ i in atTop, (S (longShelfStep C (b i)) ≤ S (b i)-(Λ (b i))^ (2:ℕ)) ∧ longShelfStep C (b i) < shelfStep C a i ∧ shelfStep C a i< b i ∧
       Short C (shelfStep C a i) i (a+1) ∧ (a-1)*Λ i ≤ gap C (shelfStep C a i) (b i) := by
    have hp:= hb.eventually ((tide_sq C hG).eventually_ge_atTop 0)
    have ht:= ran C hG hpace (zero_lt_one.trans ha)
    have hc:= lambda_leads C hG
    filter_upwards [taxed C hG 1,hp,ht,he,hc.eventually_ge_atTop (2*Real.log 2),hc.eventually_gt_atTop (4*(a+1))] with i h hx he' he hv hu
    let t:= shelfStep C a i; let y:= b i; let v:= longShelfStep C y
    change Short C y i 1 at he
    obtain ⟨(hv':Short C t i (a+1)),hz⟩:= he'
    have h1: S v ≤ S y -(Λ y)^ (2:ℕ):= (ebb_interval C hx).1
    have hL:= he.verge; have he'₁:= he; have he:= windowL C (h y he) le_rfl he.hk; have hW: Λ i/2≤ Λ y:= by linarith
    have hx := pow_le_pow_left₀ (show 0≤ (Λ i)/2 from by have := lambda_pos C i; positivity) hW 2
    have he:= hv'.verge; have ht:(a-1)*Λ i ≤ gap C t y:= by change a *_ ≤ gap C t i at hz; unfold gap at *; linarith only [hz,hL]
    refine ⟨h1,(scale_mono C.S).lt_iff_lt.mp ?_,(scale_mono C.S).lt_iff_lt.mp ?_,hv',ht⟩
    · unfold gap at *; change S v < S t
      -- need S y≤ S i
      have hq : S y≤ S i:= (scale_mono C.S).monotone (by exact he'₁.hk) -- fix name shadow
      nlinarith only [h1,hx,hq,he,mul_lt_mul_of_pos_left hu (lambda_pos C i)]
    exact sub_pos.mp (lt_of_lt_of_le (mul_pos (sub_pos.mpr ha) (lambda_pos C i)) ht)
end stopping
end YM.RG16.Guarding
