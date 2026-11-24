import YM.RG01Estimate.Papers
import YM.RG01Estimate.InteriorStage
/-!
# Rescaling and commensurate grading of the purely thermal Gaussian lens
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Courtyard
open Function Filter Set Metric MeasureTheory
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush RealTaylor Office
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F][NormedSpace ℝ F]
local notation "X" => ℝ × E
variable {b C D p v u Y : ℝ} {j k n : ℕ}

def rho (x:X):X := (x.1,x.1 • x.2)
lemma rho_mem (x:X) (hs : 1≤Y) : ‖x.2‖ <Y → ‖rho x‖ ≤ ‖x.1‖*Y:= by
  intro hx; change max _ _ ≤ _; refine max_le (le_mul_of_one_le_right (norm_nonneg _) hs) ?_
  change ‖x.1 • x.2‖ ≤ _; rw [norm_smul]; exact mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)

def expense (n:ℕ)(Y:ℝ) := (1+2*Y*2*Y*3^n)+(1+2*Y*2*Y*3^n)
lemma travel_cap (x:X) (hj:‖x.1‖≤1) (h:1≤ Y) (hp:‖x.2‖≤ Y) :
    Brush j (expense j Y) 1 rho x:= by
   let B:= ContinuousLinearMap.fst ℝ ℝ E; let D:= ContinuousLinearMap.snd ℝ ℝ E
   have hB:Brush j 1 1 B x:=Brush.linearB B hj (by rw [mul_one]; exact ContinuousLinearMap.norm_fst_le ..) zero_le_one
   have hD:Brush j Y 1 D x:=Brush.linearB D hp (by rw [mul_one]; exact (ContinuousLinearMap.norm_snd_le ..).trans h) zero_le_one
   have hk := hB.twins hD (ContinuousLinearMap.lsmul ℝ ℝ)
   have ht:= (hk.climb (mul_le_of_le_one_left (mul_nonneg zero_le_one (zero_le_one.trans h)) (ContinuousLinearMap.opNorm_lsmul_le ..)) le_rfl).trim
   let C:=1+2*Y*2*Y*3^j; have hp : 0 ≤ Y:= zero_le_one.trans h; have hc:1≤C:= le_add_of_nonneg_right (by positivity)
   apply (hB.climb hc le_rfl).pair
   apply ht.climb _ le_rfl
   simp only [one_mul,show (1:ℝ)+(1+1)=3 from by norm_num]; unfold C; have h': Y ≤ 2*Y*2*Y := le_mul_of_one_le_left hp (by linarith)
   linarith only [mul_le_mul_of_nonneg_right h' (show 0≤(3:ℝ)^j by positivity)]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {ϕ ψ : E×Poll.Body ι→ℝ} {r : E→Poll.Body ι} {M : E → Matrix ι ι ℝ}
local notation "Z" => (ball (0:E) Y)
local notation "S" => closedBall (0:Poll.Body ι) D
local notation "F" => grace ϕ ψ r M

/-- Use projection to a wider radius without assuming global φ or R regularity. -/
lemma widen {R W : ℝ} (_hD:0<D) (hv:0<v) (he:v ≤ b) (hR:1≤ R) (ht:0<W) (hc : v*R ≤ b)(hl : W≤D*R)
    (h : Golf ϕ ψ r M j D u b p) : Golf ϕ ψ r M j W u v p := by
    refine {h with pos':=hv, small':=he.trans h.small',off:=ht.le,color:=?_}
    intro z t x hz hX hw hy
    have hg : 0<R:= zero_lt_one.trans_le hR
    let b:=R*x.1; let y:=R⁻¹ • z
    have ht:= h.color y t (b,x.2) (show ‖y‖ ≤ D by unfold y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hg).le]; exact (inv_mul_le_iff₀ hg).2 (hz.trans (hl.trans_eq (mul_comm ..)))) hX (show ‖R*x.1‖< _ by rw [norm_mul, Real.norm_of_nonneg hg.le]; exact (mul_lt_mul_of_pos_left hw hg).trans_le ((mul_comm ..).trans_le hc)) hy
    rw [show visit r y t (b,x.2)= visit r z t x from (by unfold visit b y; simp only [smul_smul]; rw [show R*x.1*R⁻¹= x.1 by field_simp])] at ht
    exact ht

def voteForm (ϕ ψ : E× Poll.Body ι→ℝ) (r : E→ Poll.Body ι) (M : E→ Matrix ι ι ℝ) (i : Poll.Body ι) (x : ℝ×E) : ℝ:= Real.exp (grace ϕ ψ r M i (rho x))

section shape
variable [FiniteDimensional ℝ E]
-- u and b contours may differ after widening.
variable {w L W : ℝ} (h : Golf ϕ ψ r M j D u v p) (hp: 1≤ Y) (hu:w≤v)(hx:w*Y ≤ u)(hj : 1 ≤ j)
include h hp hu hx hj
omit hj in
lemma alone : Roll (fun i=> F i ∘ rho) S Z w (clump j (expense j Y) (fee j p D)) j:= by
   have hm (x:X)(ht:x∈corridor w Z) : ‖x.1‖<v ∧ ‖rho x‖≤ w*Y ∧ ‖(rho x).2‖ < u:= by
      have hf := mem_ball_zero_iff.mp ht.1
      have hg:= (rho_mem x hp (mem_ball_zero_iff.mp ht.2)).trans_lt (mul_lt_mul_of_pos_right hf (zero_lt_one.trans_le hp))
      exact ⟨hf.trans_le hu,hg.le,(norm_snd_le (rho x)).trans_lt (hg.trans_le hx)⟩
   refine ⟨fun i hi x hX=> ?_,fun x hX=> ?_⟩
   · obtain ⟨hh,-,ht⟩:= hm x hX
     exact composite (travel_cap _ (hh.le.trans h.small') hp (mem_ball_zero_iff.mp hX.2).le) (compel _ h (x:=rho x) ht hh (mem_closedBall_zero_iff.mp hi))
   have ht:= hm x hX
   have hh:=gallon D h (x:=rho x) ht.2.2 ht.1
   apply Measurable.stronglyMeasurable
   apply measurable_of_restrict_of_restrict_compl (s:=S) measurableSet_closedBall
   · rw [show (S).restrict (held (fun i=> F i ∘ rho) S x)= (S).restrict (fun i=> F i (rho x)) from funext fun i=> indicator_of_mem i.2 (fun i=> F i (rho x))]
     exact (continuousOn_iff_continuous_restrict.mp hh).measurable
   rw [show (Sᶜ).restrict (held (fun i=> F i ∘ rho) S x)=(fun _=>0) from funext fun i=> indicator_of_notMem i.2 (fun i=> F i (rho x))]; exact measurable_const

lemma near_formula (hk : fee j p D*(w*Y) ≤ 1) (hΞ : ∀ x∈Icc (-1:ℝ) 1,Brush j L 1 Real.exp x) :
      Roll (voteForm ϕ ψ r M) S Z w (clump j (clump j (expense j Y) (fee j p D)) L) j:= by
   refine Roll.cumulative (alone h hp hu hx) _ Real.continuous_exp ?_ measurableSet_closedBall
   intro i hi x ht
   have hf := mem_ball_zero_iff.mp ht.1; have hv:= (rho_mem x hp (mem_ball_zero_iff.mp ht.2)).trans_lt (mul_lt_mul_of_pos_right hf (zero_lt_one.trans_le hp)); have hZ: ‖(rho x).1‖<v:=hf.trans_le hu
   have hX:= (norm_snd_le (rho x)).trans_lt (hv.trans_le hx); have hb:=mem_closedBall_zero_iff.mp hi
   apply hΞ
   apply abs_le.mp
   exact (amity D h hj i hb (rho x) hZ hX).trans ((mul_le_mul_of_nonneg_left hv.le (compel D h (x:=rho x) hX hZ hb).nonneg).trans hk)
end shape
section atlas
-- power calculus for wide. here supports semantics at flat, v can shrink arbitrarily.
lemma clump_price (he : 1≤ v) (hb : b ≤ C*v^k)(hc : 0 ≤ b) (h : D ≤ p*v^j) (hD : 0 ≤ D) :
     clump n b D ≤ clump n C p *v^(k*n+j) := by
   unfold clump; simp only [mul_one]
   have hv : 0<v:= zero_lt_one.trans_le he
   have hk : 1≤ v^k:= one_le_pow₀ he
   have hh : 1+(1+b) ≤ (1+(1+C))*v^k := by nlinarith only [hb,hk]
   calc
     _ ≤ n.factorial*(p*v^j)*((1+(1+C))*v^k)^n := by have he : 0 ≤ p*v^j:= hD.trans h; gcongr
     _ = _ := by rw [mul_pow,pow_add,pow_mul]; ring

def feeExponent (j:ℕ):= j+2
lemma quote_fee (j:ℕ) {q : ℝ} (h : 0<q)(hP:0≤p):
     fee j p q ≤ fee j p 1 * (1+q)^(feeExponent j) := by
    let v := 1+q; have hv:1≤v:=le_add_of_nonneg_right h.le
    let p' := p; let s:=spanE p 1
    have hs : spanE p q ≤ s*v^1 := by unfold s spanE v; rw [pow_one]; nlinarith only [mul_nonneg hP h.le,h.le]
    have ht : clump j (spanE p q) p ≤ clump j s p * v^j:=by
       have he:=clump_price (n:=j) (j:=0) hv hs (show 0 ≤ spanE p q by unfold spanE; positivity) (show p ≤ p*v^0 by rw [pow_zero,mul_one]) hP
       rw [one_mul,add_zero] at he; exact he
    have hw : q≤v:= le_add_of_nonneg_left zero_le_one
    have hk:0≤ clump j (spanE p q) p:= by unfold clump spanE; positivity
    have hxx:0≤ clump j s p:= by unfold clump s spanE; positivity
    have hV : acrossE j p q ≤ acrossE j p 1 * v^(feeExponent j) := by
       apply le_trans (mul_le_mul hw (mul_le_mul hw ht hk (zero_le_one.trans hv)) (mul_nonneg h.le hk) (zero_le_one.trans hv))
       unfold acrossE feeExponent; rw [pow_add]; unfold s; exact le_of_eq (by ring)
    let a:=v^(feeExponent j)
    have hh:clump j (spanE p q) p ≤ clump j s p*a:= ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv (Nat.le_add_right j 2)) hxx)
    unfold fee; simp only [add_mul]; exact add_le_add (add_le_add (add_le_add (le_mul_of_one_le_right hP (one_le_pow₀ hv)) (le_mul_of_one_le_right hP (one_le_pow₀ hv))) (add_le_add hV hV)) (add_le_add hh hh)

def priceExponent (j:ℕ):= feeExponent j * j + 0
variable [FiniteDimensional ℝ E]
lemma atlas_formula {L : ℝ} (h : Golf ϕ ψ r M j D u v p) (hD:0<D)(hj:1≤ j)(hp : 1≤Y)(hE:0≤ L) (he : ∀ x∈ Icc (-1:ℝ) 1,Brush j L 1 Real.exp x) : Atlas (voteForm ϕ ψ r M) Z (priceExponent j) j (clump j (clump j (expense j Y) (fee j p 1)) L) := by
    constructor; intro q hq
    let R := 1+q/D; let w:= v/R
    have hz : 0<q/D:= div_pos hq hD; have hv:1≤ R:= le_add_of_nonneg_right hz.le; have hr:0<R:=zero_lt_one.trans_le hv
    have h':0<w:= div_pos h.pos' hr
    have hV : Golf ϕ ψ r M j q u w p := widen hD h' (div_le_self h.pos'.le hv) hv hq (div_mul_cancel₀ v hr.ne').le (show q≤D*R by unfold R; rw [mul_add,mul_comm D (q/D),div_mul_cancel₀ q hD.ne']; linarith) h
    let f:=fee j p q
    have h₀ : ‖(0: E)‖ < u:= by rw [norm_zero]; exact h.pos
    have hk : 0≤p:= (h.curve _ h₀).nonneg
    have hf :0≤f:= by unfold f fee acrossE spanE clump; positivity
    have hy:0<Y:= zero_lt_one.trans_le hp
    let t := min w (min (u/Y) (((1+f)*Y)⁻¹))
    have h1:0<(1+f)*Y:=by positivity
    have ht:0<t:= lt_min h' (lt_min (div_pos h.pos hy) (inv_pos.mpr h1))
    have hs : t≤w:=min_le_left ..
    have hu:t≤ min (u/Y) (((1+f)*Y)⁻¹):= min_le_right ..
    have hW : (1+f)*Y*t ≤ 1:= (mul_le_mul_of_nonneg_left (hu.trans (min_le_right ..)) h1.le).trans_eq (mul_inv_cancel₀ h1.ne')
    have hh:= near_formula hV hp hs ((le_div_iff₀ hy).1 (hu.trans (min_le_left ..))) hj (show f*(t*Y) ≤ 1 by nlinarith only [hW,mul_pos ht hy]) he
    let V:= 1+q; have hφ : 1≤ V:= le_add_of_nonneg_right hq.le
    have hfee:=quote_fee j hq hk
    have hE' : 0≤expense j Y:= by unfold expense; positivity
    have hl : clump j (expense j Y) f ≤ clump j (expense j Y) (fee j p 1)*V^(feeExponent j):= by
      have he := clump_price (n:=j) hφ (show expense j Y≤ expense j Y*V^0 by simp) hE' hfee hf
      rw [zero_mul,zero_add] at he; exact he
    have ht:= clump_price (n:=j) hφ hl (show 0 ≤ clump j (expense j Y) f by unfold clump; positivity) (show L≤L*V^0 by simp) hE
    exact ⟨t,show 0<t from (by assumption),hh.of_le ht le_rfl le_rfl⟩
end atlas
end YM.RG01Estimate.Courtyard
