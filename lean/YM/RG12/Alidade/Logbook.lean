import YM.RG12.Alidade.Chrono
import YM.RG12.Rail.Wax
/-! # Cumulative Price of the quantitative lead accuracy -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Finset Wilson Lattice RG Source Real Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer Commission Rail
open scoped Topology BigOperators Classical
variable {G:Gauge}(Y:Levels G)(h:G.Simple)
local notation "χ"=> Y.clock.hatBeta
local notation "b"=> Y.clock.monitor
local notation "σ"=> G.slopeConstant
include h
lemma face_low (i:ℕ) : (i:ℝ) * (σ*Real.log 3) ≤ χ i:=by
   have hp:=epoch_pace Y i; unfold epoch at hp
   have hb:= Y.clock.bar_pos
   have hz:(i:ℝ)*Real.log 3 ≤ Y.S.scale i:=(le_div_iff₀ arc3).mp (le_of_add_le_add_left hp)
   unfold Calendar.hatBeta; nlinarith only [hb,mul_le_mul_of_nonneg_left hz (Gauge.slopeConstant_pos h).le]
-- reciprocal bill powers, cost after response (d fixed)
omit Y h in
lemma bill_inv (x t:ℝ): bill (-t) x=(bill t x)⁻¹:=by unfold bill; rw [mul_neg,Real.exp_neg]
omit h in
lemma charge (x:ℝ)(i:ℕ) : fineprint Y (Nat.ceil x) i ≤1:= by
    have hq:0≤cut₀ (Nat.ceil x):=by unfold cut₀ σ₀; positivity
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [hq])) -- emph
-- effective nth cutoff lower bound for within-tail summation. square comparison avoids sqrt sums
lemma faces {n k:ℕ}(hx:Real.sqrt (χ k) ≤ (n:ℝ)) : Real.sqrt (χ k)*(σ*Real.log 3) ≤ χ n :=by
   exact (mul_le_mul_of_nonneg_right hx (mul_pos (Gauge.slopeConstant_pos h) arc3).le).trans (face_low Y h _)
private lemma era {n k:ℕ}(he:Real.sqrt (χ k) ≤ (n:ℝ))(_hk : 1 ≤ Real.sqrt (χ k)*(σ*Real.log 3)):
   Real.log (χ k)/2 + Real.log (σ*Real.log 3) ≤ Real.log (χ n):=by
   have hv:=mul_pos (Gauge.slopeConstant_pos h) arc3
   have hz:=year Y k
   have hf:=Real.log_le_log (mul_pos (Real.sqrt_pos.mpr hz) hv) (faces Y h he)
   simpa [Real.log_mul (Real.sqrt_pos.mpr hz).ne' hv.ne', Real.log_sqrt hz.le] using! hf
-- actual logarithms squared compare down to sqrt cutoff. independent simple gauge.
theorem heat_sum : ∀ᶠ k:ℕ in atTop, ∀ i:ℕ, Real.sqrt (χ k) ≤ (i:ℝ)→ (1/4:ℝ) * boil (χ k) ≤ boil (χ i):=by
    have hh:= year_late Y h; let a := σ * Real.log 3;have ha :0 < a:=mul_pos (Gauge.slopeConstant_pos h) arc3
    have hv:=Real.tendsto_log_atTop.comp hh;let P:=Real.log 3;have hp:0<P:=arc3
    have hq:=Real.tendsto_log_atTop.comp hv
    filter_upwards [(Filter.Tendsto.atTop_mul_const ha (Real.tendsto_sqrt_atTop.comp hh)).eventually_ge_atTop 1, hv.eventually_ge_atTop (-6 * Real.log a), hq.eventually_ge_atTop (2*P)] with k hk hi hf i hx
    let u:=Real.log (χ k);let v:= Real.log (χ i);let t:= Real.log u
    have hu:0<u:=Real.log_pos (Y.fits.delayed _)
    change -6*Real.log (σ * Real.log 3) ≤ u at hi; change 1 ≤ Real.sqrt (χ k)*(σ * Real.log 3) at hk
    have he: u/3 ≤ v:=by linarith only [era Y h hx hk, hi]
    have hr: t-P ≤ Real.log v:=by
       have he':= Real.log_le_log (div_pos hu (by norm_num)) he; rw [Real.log_div hu.ne' (by norm_num)] at he'; exact he'
    unfold boil Perch.y
    change 1/4 * t^2 ≤ Real.log v ^ 2
    change 2*P ≤ t at hf
    nlinarith only [hr,hf,hp]

-- meter exponent/g bridge eventually
omit h Y in
lemma boil_in (t r:ℝ)(hr:0 < r): ∀ᶠ x in atTop,bill t x ≤ x^r:=by
   have h:= YM.Vac.Numbers.cost t r hr
   simpa only [YM.Vac.Numbers.P,← Real.exp_mul] using! h -- exp_rpow ?
-- reciprocal
lemma mass_control (t:ℝ) : ∀ᶠ k:ℕ in atTop, Real.sqrt (χ k) ≤ bill (-t) (χ k)*χ k:=by
   have hχ:=year_late Y h
   filter_upwards [hχ.eventually (boil_in t (1/2) (by norm_num))] with k hk
   let v:= Real.sqrt (χ k); have hp:0 < v:=Real.sqrt_pos.mpr (year Y k)
   let w:=bill t (χ k); have hw:0<w:=Real.exp_pos _
   rw [← Real.sqrt_eq_rpow] at hk
   rw [bill_inv,inv_mul_eq_div, le_div_iff₀ hw]
   nlinarith only [mul_le_mul_of_nonneg_left hk hp.le,Real.sq_sqrt (year Y k).le]
-- conversion to field price. Rate beats all inverse of log coupling powers inside exp.
def halo (Z:Levels G)(n k:ℕ):= bill (-(cut₀ n/4)) (Z.clock.hatBeta k)
def quote (Z:Levels G)(n k:ℕ):= halo Z n k * (Z.clock.hatBeta k)
lemma survives (n:ℕ)(K:ℝ) (hK:0 ≤ K) : ∃ D:ℝ,0≤D∧∀ᶠ k in atTop,(∑ i∈Finset.range k, min 1 (K*fineprint Y n i)) ≤ D*quote Y n k:=by
   let a:ℝ:=σ* Real.log 3; have ha:0<a:= mul_pos (Gauge.slopeConstant_pos h) arc3
   let D:= 2+K*a⁻¹
   have hs(K):0 ≤ cut₀ K:=by unfold cut₀ σ₀; positivity
   have hl:Tendsto (Real.sqrt ∘ χ) atTop atTop:=Real.tendsto_sqrt_atTop.comp (year_late Y h)
   let ψ (k):= halo Y n k; have hr(k):0 ≤ ψ k:=(Real.exp_pos _).le
   refine ⟨D,by unfold D; positivity,?_⟩
   filter_upwards [heat_sum Y h, mass_control Y h (cut₀ n/4),hl.eventually_ge_atTop 1] with k hk hw hh
   let P:ℝ:=Real.sqrt (χ k); let m:ℕ:= Nat.ceil P
   let S:=Finset.range k; let T:=S∩Finset.range m
   have hT:T ⊆ S:=Finset.inter_subset_left
   let e(i):= min 1 (K*fineprint Y n i)
   have ht(i:ℕ)(hi:i∈ S\T):Real.sqrt (χ k) ≤ (i:ℝ):=by
      obtain ⟨h1,h2⟩:=Finset.mem_sdiff.mp hi
      have ho:m ≤ i:=le_of_not_gt (fun h=>h2 (Finset.mem_inter.mpr ⟨h1,mem_range.mpr h⟩))
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr ho)
   have h0(k):0≤e k:=by unfold e fineprint; exact le_min (by norm_num) (mul_nonneg hK (Real.exp_pos _).le)
   have hp : ∑ i∈S\T,e i ≤ (k:ℝ)*(K* ψ k):=by
      have he(i)(hi:i∈S\T):e i ≤ K*ψ k:=by
         apply (min_le_right ..).trans; apply mul_le_mul_of_nonneg_left _ hK
         unfold fineprint ψ halo bill
         apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_right (hk i (ht i hi)) (hs n)]
      have he':0 ≤ K*ψ k:=mul_nonneg hK (hr k)
      calc
        _ ≤ ∑ _i∈S\T, K*ψ k:= sum_le_sum he
        _ ≤ _ := by rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ he'; exact_mod_cast (show (S\T).card ≤ k from by rw [← card_range k]; exact card_le_card sdiff_subset) -- sdiff lemma args?
   have hi:0 ≤ P:= Real.sqrt_nonneg _
   have he:∑ i∈T,e i ≤ 2*P:=by
     have ht:(m:ℝ)<P+1:=Nat.ceil_lt_add_one hi
     calc
       _ ≤ ∑ _i∈T, (1:ℝ):=sum_le_sum (fun i _=>min_le_left ..)
       _ ≤ (m:ℝ):=by simpa using! (show ((Finset.card T:ℕ):ℝ) ≤ ↑m from by exact_mod_cast (show T.card ≤ m from by rw [← card_range m]; exact card_le_card inter_subset_right))
       _ ≤ _:=by change 1 ≤ P at hh; linarith
   have hcnt: (k:ℝ) ≤ a⁻¹ * χ k:=by rw [inv_mul_eq_div,le_div_iff₀ ha]; exact face_low Y h k
   change ∑ i ∈S,e i ≤ _
   rw [← sum_sdiff hT]; apply (add_le_add hp he).trans
   have he:= mul_le_mul_of_nonneg_right hcnt (mul_nonneg hK (hr k))
   unfold quote; change P≤ ψ k *_ at hw
   change _ ≤ D*(ψ k*_); unfold D; nlinarith only [he,hw]
-- absolute tab conversion price. D hidden.
lemma radian (n:ℕ) : ∀ (p P:ℕ) (e : ℕ→ℝ) (K:ℝ), 0≤K→ (∀ i,e i ≤ min 1 (K*fineprint Y n i)) → ∃ D:ℝ,0≤D ∧ ∀ᶠ k in atTop, (χ k)^p* interest e P k ≤ exp (D*quote Y n k):=by
   intro p P e K hk he
   obtain ⟨D,Hd,H⟩:=survives Y h n K hk
   have hf:Tendsto (Real.sqrt ∘ χ) atTop atTop:=Real.tendsto_sqrt_atTop.comp (year_late Y h)
   have hh:=mass_control Y h (cut₀ n/4)
   let B:=2*p+D*P
   refine ⟨B,by unfold B; positivity,?_⟩
   filter_upwards [hh,H] with k hk hi
   rw [← exp_log (year Y k),← Real.exp_nat_mul] -- first χ rewrites RHS? all?
   unfold interest; rw [←Real.exp_add]; apply Real.exp_monotone
   let t:=Real.sqrt (χ k); have ht:0<t:=Real.sqrt_pos.mpr (year Y k)
   have ha: log (χ k) ≤ 2*t:=by
      have he:=Real.log_le_sub_one_of_pos ht; have hs:= Real.log_sqrt (year Y k).le
      linarith only [he,hs]
   have he' : log (χ k) ≤ 2* quote Y n k:=ha.trans (mul_le_mul_of_nonneg_left hk (by positivity))
   unfold B; nlinarith only [mul_le_mul_of_nonneg_right ((Finset.sum_le_sum (s:=range k) (fun i _=> he i)).trans hi) (Nat.cast_nonneg (α:=ℝ) P),mul_le_mul_of_nonneg_left he' (Nat.cast_nonneg (α:=ℝ) p)]
end YM.RG12.Alidade
