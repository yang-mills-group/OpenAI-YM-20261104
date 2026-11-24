import YM.MSbar.Bristol.Ohio
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Lodge Measuring RawP
variable {G:Gauge}{c:Side}{σ:Type}[Fintype σ][DecidableEq σ]
variable {G:Gauge}{c:Side}{p q m:ℕ} (R:Rep G c)(Z:Nesting G c)(b:PowerSeries ℝ)
local notation "X₀"=>Positions (Primary c G)
local notation "X"=> Pot (Primary c G)
local notation "Ω"=>ink c R.clip R.path
local notation "V"=> PowerSeries ℝ
local notation "φ"=>film R Z
local notation "S"=> bley b Z Ω
variable (u r s:ℝ)
local notation "μ"=>PowerSeries.coeff
variable {ℓ:Primary c G→Site c}{A B a v w t κ:ℝ}
variable (hp:0<u)(ht:Belt p b ≤ A)(hf:Belt p b⁻¹≤ A)(hc:|u|≤ A)(hx:u⁻¹≤ A)(hh:1≤A)(hr:0≤ s)(hk:s ≤1)(hb:μ 0 b=1)
variable (hZ:Kind Z)(he:∀ i ≤ p,Tin ℓ a m q w (PowerSeries.coeff i Z) B)
local notation "δ"=> surf b s u p
include hp ht hf hc hx hh hr hk hb
lemma pledge (hg:v≤u)(hv:0 < v) (hu:0 ≤ taste p b s): |u-taste p b s|≤ v⁻¹*(|surf b s u p|+2*s^(p+1)*A^2):=by
     let y:= taste p b s; have he:0≤ y:=hu; have hB: |u^2-y^2| ≤ |δ|+2*s^(p+1)*A^2:=by
          let z:= taste p (b^2) s; have ht':|u^2-z|=|δ|:=abs_sub_comm ..; refine (abs_sub_le _ z _).trans (add_le_add ht'.le ((taste_power b p 2 hr hk).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Belt_pos ..) ht _) (by positivity))))
     rw [mul_comm v⁻¹,← div_eq_mul_inv,le_div_iff₀ hv]; apply le_trans _ hB; calc
        _ ≤ |u-y| * (u+y):=mul_le_mul_of_nonneg_left (hg.trans (le_add_of_nonneg_right he)) (abs_nonneg _)
        _ = |u^2-y^2| :=by rw [show u^2-y^2=(u-y)*(u+y) by ring]; rw [abs_mul,abs_of_nonneg (add_nonneg hp.le he)] -- nth fix
noncomputable def priceZ (K:ℝ)(p:ℕ):=∑ i∈range (p+1),∑ j∈range (i+2+1),tonK K j i -- Ton order with Scout call
local notation "J!"=> s*|u-taste p b s|+(A+1)*s^(p+1)
lemma costsK (i:ℕ)(hi:0 < i)(h:i≤p) (j:ℕ):|pegsK b s u p i j|≤ tonK A j i*(s*|u-taste p b s| +(A+1)*s^(p+1)):=by
     let x:= p-i; let V':=tonK A j i; have hV:0≤ V':=by unfold V' tonK; have hA:0≤ A:=zero_le_one.trans hh; positivity
     have h₀:x≤p:= Nat.sub_le ..; let U:=taste p b s; let g:= taste x b s; unfold pegsK; rw [abs_mul,abs_of_nonneg (pow_nonneg hr _)]; apply (mul_le_mul_of_nonneg_left (scent b u hb hp hc hx (mini ht h₀) (mini hf h₀) hh hr hk j i) (pow_nonneg hr _)).trans;
     have hP:s^(p+1)= s^i*s^(x+1):=by rw [← pow_add,show p+1=i+(x+1) from (by unfold x; omega)] -- recursive x? x alias
     have ht:s^i*|u-g| ≤ s*|u-U|+s^(p+1)*A:=by
          refine le_trans (mul_le_mul_of_nonneg_left ((abs_sub_le u U g).trans (add_le_add_right (remainderM ht h₀ hr hk) _)) (pow_nonneg hr _)) ?_; rw [mul_add]; refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_of_le_one hr hk (show 1 ≤ i from hi)) (Eq.le (pow_one s))) (abs_nonneg _)
          rw [← mul_assoc,← hP]
     rw [mul_left_comm (s^i) (tonK ..),mul_add (s^i)]; refine mul_le_mul_of_nonneg_left ?_ hV; change s^i*|u-g| + s^i*s^(x+1) ≤ _; rw [←hP]; exact (add_le_add_left ht _).trans_eq (by unfold U; ring)
variable (hw: 0 < w)
include he hZ hw
lemma gems : Tin ℓ a m q w (pegs Z b s u p) (priceZ A p*((s*|u-taste p b s| +(A+1)*s^(p+1))*B)) :=by
     let T:= s*|u-taste p b s| +(A+1)*s^(p+1); have hT:0≤ T:= by have hA:0 ≤ A:= zero_le_one.trans hh; unfold T; positivity
     have hB: 0 ≤B:= (he _ le_rfl).dec
     unfold pegs priceZ; rw [Finset.sum_mul]; refine Tin.pool hw (lampZ Z b s u p) _ _ ?_; intro i hi; unfold lampZ; rw [Finset.sum_mul]; refine Tin.pool hw _ _ _ ?_; intro j hj
     by_cases hz:i=0; · subst i; rw [hZ,map_zero,smul_zero, ←show MvPolynomial.C (σ:=Primary c G) (R:=ℝ) 0=0 from C_0]; refine Tin.it hw (Tin.constant hw 0 (le_refl _)) ?_ le_rfl; change 0 ≤ _; apply mul_nonneg _ (mul_nonneg hT hB); unfold tonK; have hp:=lt_of_lt_of_le zero_lt_one hh; positivity
     have ht':= Bronze.pers (n:=j) (he _ (Nat.lt_succ_iff.mp (mem_range.mp hi))) -- n binder
     apply Tin.it hw (Tin.real hw (pegsK b s u p i j) ht'); exact (mul_le_mul_of_nonneg_right (costsK b u s hp ht hf hc hx hh hr hk hb i (by omega) (Nat.lt_succ_iff.mp (mem_range.mp hi)) j) hB).trans_eq (by ring);exact le_rfl
lemma tones (v:ℝ)(hv: v≤u)(hu:0<v)(hg:0 ≤ taste p b s): Tin ℓ a m q w (pegs Z b s u p) (priceZ A p * ((s*v⁻¹*|δ| +(s*v⁻¹*(2*s^(p+1)*A^2)+(A+1)*s^(p+1)))*B)):=by
     have h':0 ≤ priceZ A p:=by unfold priceZ; have hA:=zero_lt_one.trans_le hh; refine sum_nonneg fun i _=> sum_nonneg fun j _=> by unfold tonK; positivity
     have hg:= pledge b u s hp ht hf hc hx hh hr hk hb hv hu hg; refine Tin.it hw (gems Z b u s hp ht hf hc hx hh hr hk hb hZ he hw) ?_ le_rfl; apply mul_le_mul_of_nonneg_left _ h'; apply mul_le_mul_of_nonneg_right _ (he _ le_rfl).dec; exact (add_le_add_left (mul_le_mul_of_nonneg_left hg hr) _).trans_eq (by ring)
end YM.MSbar.Bristol
