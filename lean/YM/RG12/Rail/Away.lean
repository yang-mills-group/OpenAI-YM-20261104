import YM.RG12.Rail.Paper
/-!
# Strengthened Mural-Ray Port (discrete covariance and expensive form sizes)

Here absorb one power of the calendar monitor in the image bound while keeping
analytic suppliers unchanged. Gives usable window width along SPATIAL RAYS up to
that monitor. Adapted from West/Erl, Jolly and Next.RANK.Displacement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Set Filter Lattice Wilson RG Next.Rank Next.Rank.Atlas Station Next.Rank.Value
open Glimmer Prayer Configuration Perch Marker Glyph Cells Market Read Dock Camp Beamer Normal
open CellsInt Wall Maxwell
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {A:Levels G}{n d:ℕ}(H:G.Simple)
variable {a:Points n} (ha:a∈conf n) {b:ℝ} (hb:0 < b)
set_option quotPrecheck false
local notation "M!" k:max=> Station.mag A b k
local notation "Y" k:max=> (A).clock.monitor k
include H hb
lemma off_budget (ε:ℝ)(he:0 < ε): ∀ᶠ k in atTop,
    ∀ i j:Cover, street i ≤ wood A k→street j ≤ wood A k→ ‖(M! k)⁻¹ • (mapZ i - mapZ j)‖ ≤ ε:=by
    filter_upwards [(hat_rate A H).eventually (transports (show b/2<b by linarith) (4/ε)),
    (hat_rate A H).eventually (zone_power 1 (show 0<b/2 by linarith))] with k h1 h2 i j hi hj
    have hv:=mag_pos A b k; let v:= wood A k
    have hy : ‖mapZ i-mapZ j‖ ≤ 2*↑v := by
       refine (norm_sub_le ..).trans ?_; linarith only [(norm_road i).trans (show (street i:ℝ)≤v from by exact_mod_cast hi),(norm_road j).trans (show (street j:ℝ)≤v from by exact_mod_cast hj)]
    rw [norm_smul,norm_inv, Real.norm_of_nonneg hv.le]
    refine (mul_le_mul_of_nonneg_left hy (inv_pos.mpr hv).le).trans ?_
    rw [← div_eq_inv_mul,div_le_iff₀ hv]
    simp only [pow_one] at h2
    unfold v; field_simp at h1; change (↑(lengthW _):ℝ) ≤ _ at h2; rw [mag_bill]; unfold wood clim; nlinarith only [h1,h2,show 0 < bill b (A.clock.hatBeta k) from Real.exp_pos _,he]

omit hb in
-- d priori upper bound on n.v: port image. radiant_cost A handles powers of M (loglog).
lemma summery (u : ℕ) (h : 6 ≤ b) {c C : ℝ} (hc : 0 < c) (_hC : 1 ≤ C) : ∀ᶠ k in atTop,∀ p : ℕ,∀ z : E4,
    let m:=mag A b k; let s:=clim A k
    c*m ≤ ‖z‖ → ‖z‖ ≤ C*m*(Y k) → m^(4+u)*bill 1 s * stature u z ((A.S.side k p).val:ℝ) ≤ bill (-4) s := by
  have hb : 0<b := by linarith
  filter_upwards [radiant_cost A 2 (2*(1+C)) (-4) b (4+u) H,
    (hat_rate A H).eventually (transports (show (1:ℝ) < -4+b by linarith) (2/(c^(u+5))))] with k hr ht p z
  let N := (A.S.side k p).val
  intro M s hL hR
  have hw : 1 ≤ M := by change 1 ≤ mag _ _ _; rw [mag_bill]; exact Glimmer.costed b _ hb.le
  have hY : 0 < bill 1 s := Real.exp_pos _
  have hp : 0 < M := zero_lt_one.trans_le hw
  have ht' : 2*(M^(4+u)*bill 1 s* (1/‖z‖^(u+5))) ≤ bill (-4) s := calc
    _ ≤ 2*(M^(4+u)*bill 1 s * (1/(c*M)^(u+5))) := by gcongr
    _ ≤ _ := by
      have he : (2/c^(u+5))*bill 1 s ≤ bill (-4) s * M := by
        change _ ≤ bill (-4+b) _ at ht; rw [← overlap] at ht; rw [show M=_ from mag_bill ..]; exact ht
      rw [show 2*(M^(4+u)*bill 1 s*(1/(c*M)^(u+5)))=(2/c^(u+5))*bill 1 s / M by rw [mul_pow,show u+5=(4+u)+1 by omega,pow_succ M]; field_simp]; exact (div_le_iff₀ hp).2 he
  have hv : (Y k)=bill 1 s:=fire_bill ..
  rw [hv] at hR
  have hy : 1 ≤ bill 1 s := Glimmer.costed 1 _ zero_le_one
  have ha : (1+‖z‖) ≤ (1+C)*M*bill 1 s := by nlinarith [one_le_mul_of_one_le_of_one_le hw hy]
  have hN : 0 < (N:ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ha hN.le) (show 0 ≤ M^(4+u)*bill 1 s from by positivity)
  have hf : M^(4+u)*bill (1+1) s*(2*(1+C)*M/(N:ℝ)) ≤ bill (-4) s := by convert hr p using 1; norm_num [M,s,N]
  unfold stature; rw [mul_add]; let V:= M^(4+u)*bill 1 s; change 2*(V*_) ≤ _ at ht'
  apply (add_le_add_right hh _).trans
  rw [← overlap,show M^(4+u)*(bill 1 s*bill 1 s)*(2*(1+C)*M/(N:ℝ))=2*(V*((1+C)*M*bill 1 s/N)) by dsimp [V]; ring] at hf
  change V*_+V*_≤_; linarith only [ht',hf]

include ha
lemma range_R (i j:Fin n)(hi:i≠j)(L S:Degree G) :
    ∃ C c : ℝ, 0<c ∧ 1≤C ∧ ∀ᶠ k in atTop,∀ x:Points n, Anemos a (Y k) (tested A b k x)→ ∀ u w : Cover, street u ≤ wood A k → street w ≤ wood A k →
      let K:=moved x A b i j k u w
      let m:=mag A b k
      c*m≤ ‖K‖ ∧ ‖K‖ ≤ C*m*(Y k) ∧ ‖gleam L S (m⁻¹ • K)‖≤C := by
  let q:= a i - a j
  have h : q∈away := sub_ne_zero.mpr ((ha:Injective a.ofLp).ne hi)
  let c:= ‖q‖/2
  have hf : 0 < c := half_pos (norm_pos_iff.mpr h)
  let C:= 1+‖q‖+‖gleam L S q‖
  have hv := (gleam_diff L S q h).continuousAt (open_away.mem_nhds h)
  have hx : ∀ᶠ z in 𝓝 q, z∈away∧c ≤ ‖z‖ ∧ ‖z‖ ≤ C ∧ ‖gleam L S z‖ ≤ C := by
    refine (show ∀ᶠ z in 𝓝 q,z∈away from open_away.mem_nhds h).and ((continuous_norm.continuousAt.eventually (le_mem_nhds (half_lt_self (norm_pos_iff.mpr (show q≠0 from h))))).and ((continuous_norm.continuousAt.eventually (ge_mem_nhds ?_)).and
      (hv.norm.eventually (ge_mem_nhds ?_))))
    · change ‖q‖<C; unfold C; linarith [norm_nonneg (gleam L S q)]
    change ‖_‖<C; unfold C; linarith [norm_nonneg q]
  obtain ⟨ε,hε,hx⟩ := Metric.mem_nhds_iff.mp hx
  have he : 1≤C := by unfold C; linarith [norm_nonneg q,norm_nonneg (gleam L S q)]
  refine ⟨C,c,hf,he,?_⟩
  filter_upwards [off_budget (A:=A) H hb (ε/2) (half_pos hε)] with k hk x hQ u w hu hw K m
  obtain ⟨t,⟨ht,hh⟩,he'⟩:=hQ
  have Ht:= zero_lt_one.trans_le ht
  let V:= m⁻¹ • (mapZ u-mapZ w)
  let z:= q+t⁻¹ • V
  have hE : m⁻¹ • K=t • z:=by
     rw [show m⁻¹ • K = _ from settled ..,he']; change (t • a i-t • a j+V)=_; unfold z q; rw [smul_add,smul_smul,mul_inv_cancel₀ Ht.ne',one_smul,smul_sub]
  have hz:z∈Metric.ball q ε:=by
     rw [Metric.mem_ball,dist_eq_norm]; unfold z; rw [add_comm,add_sub_cancel_right,norm_smul,norm_inv,Real.norm_of_nonneg Ht.le]; exact ((mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ ht)).trans (hk u w hu hw)).trans_lt (half_lt_self hε)
  obtain ⟨hg,h₁,h₂,H₃⟩:= hx hz
  have hm : 0 < m:=mag_pos ..
  have hv : ‖K‖/m=t*‖z‖:= by rw [div_eq_inv_mul]; rw [← show ‖(m⁻¹:ℝ) • K‖=m⁻¹ * ‖K‖ from by rw [norm_smul,norm_inv,Real.norm_of_nonneg hm.le],hE,norm_smul,Real.norm_of_nonneg Ht.le]
  constructor
  · rw [← le_div_iff₀ hm,hv]; exact h₁.trans (le_mul_of_one_le_left (norm_nonneg _) ht)
  rw [mul_right_comm,←div_le_iff₀ hm,hv,hE]
  constructor
  · rw [mul_comm]; exact mul_le_mul h₂ hh Ht.le (zero_le_one.trans he)
  apply le_trans _ H₃
  have hY:= congr_arg norm (grown L S Ht z hg)
  have hT:{j:Degree G}→1 ≤ amount t j:=fun {_}=>one_le_pow₀ ht
  rw [norm_mul,norm_mul, Real.norm_of_nonneg (zero_le_one.trans hT), Real.norm_of_nonneg (zero_le_one.trans hT)] at hY
  exact (le_mul_of_one_le_left (norm_nonneg _) (one_le_mul_of_one_le_of_one_le hT hT)).trans_eq hY
end YM.RG12.Rail
