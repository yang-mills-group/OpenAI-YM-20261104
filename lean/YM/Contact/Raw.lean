import YM.Contact.Stencil

/-! Extension in the total relative frame (unsymmetrized at this stage) and quantitative
bounds. Strict support equality is proved separately. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts
open Set Metric Filter Function MeasureTheory LinearMap
open scoped Topology ContDiff BigOperators Pointwise
variable {k d:ℕ}
set_option quotPrecheck false
local notation "E"=>Points k

/-- Coefficient cost on all normalized dilates in relative coordinates. -/
def Quoted (s:ℝ)(d j:ℕ) (F:Trial E→ℂ) := ∀ R≥1,∀ {e:ℝ},0<e→ ∃ C:ℝ,0≤C ∧ ∀ r:ℝ,0 < r → r ≤ min 1 s → ∀  {φ:Trial E} {B:ℝ},(support ⇑φ) ⊆ Metric.closedBall 0 R → Major j φ B → ‖F (shrinking r φ)‖ ≤ C*r^(-(d:ℝ)-e)*B

lemma unscaled (s:ℝ)(hs:0<s) {j:ℕ}{F:Trial E→ℂ} (h:Quoted s d j F): Controlled F j :=by
   intro R _hR; let q:= min 1 s; let Q:=max 1 (q⁻¹*R); have hq:0<q:=lt_min zero_lt_one hs
   obtain ⟨c,hc,he⟩:=h Q (le_max_left ..) (by norm_num:0<(1:ℝ))
   let D:= Module.finrank ℝ E
   let z:=(q⁻¹^D)⁻¹*(max 1 (q⁻¹)⁻¹)^j
   have hz:0 ≤ z:=by dsimp only [z]; positivity
   refine ⟨c*q^(-(d:ℝ)-1)*z,by positivity,?_⟩
   intro φ hφ B hB
   let ψ:=shrinking q⁻¹ φ
   have hψ:support ⇑ψ ⊆ Metric.closedBall 0 Q:=by
     intro x hx; obtain ⟨y,hy,rfl⟩:=(shrink_support q⁻¹ (inv_pos.mpr hq).ne' (φ:E→ℂ) hx)
     have hy':=mem_closedBall_zero_iff.mp (hφ hy|>.2)
     rw [mem_closedBall_zero_iff, norm_smul_of_nonneg (inv_pos.mpr hq).le];exact (mul_le_mul_of_nonneg_left hy' (inv_pos.mpr hq).le).trans (le_max_right ..)
   have hψ' : Major j ψ (z*B):=shrinking_major (inv_pos.mpr hq) hB
   convert he q hq le_rfl hψ hψ' using 1
   · exact congr_arg (fun ψ:Trial E=>‖F ψ‖) (TestFunction.ext fun x=>by simp [ψ,shrinking_apply,shrink_apply,smul_smul,hq.ne',inv_pow])
   ring

namespace Manage
variable {f : Points k →ℂ} (H:Manage f d)
include H
lemma priced (s:ℝ)(hs:0<s)(R:ℝ)(hR:1≤R){ε:ℝ}(hε:0<ε): ∃ C:ℝ, 0 ≤ C∧
 ∀ {r:ℝ},0 < r → r ≤ min 1 s → ∀  {φ:Trial E} {B:ℝ}, (support ⇑φ) ⊆ Metric.closedBall 0 R → Major (d+1) φ B → Summable (fun i=>‖visit H s i (shrinking r φ)‖) ∧ ‖∑' (i:ℤ),visit H s i (shrinking r φ)‖ ≤ C*r^(-(d:ℝ)-ε)*B:= by
    let e:=min ε (2:ℝ)⁻¹
    have he:0<e:=lt_min hε (by positivity)
    have he':e<1:=lt_of_le_of_lt (min_le_right ..) (by norm_num)
    let m:=degree k d
    have hk: (m:ℝ) + 1 ≤ (m+1).toNat := by exact_mod_cast (Int.toNat_le.mp (le_refl (m+1:ℤ).toNat))
    obtain ⟨M,hM,h⟩:=dyadic_payment («E»:=ℂ) (show 0<(m+1).toNat-(m:ℝ)-e by linarith only [he',hk]) he
    obtain ⟨C,hC,hp⟩:=preview H s hs R hR he he'
    refine ⟨C*M,mul_nonneg hC hM,?_⟩
    intro r hr hr' φ B hφ hφ'; have hB:= hφ'.nonneg
    refine (h hr _ _ (show 0 ≤ C*r^(-(d:ℝ)-e)*B by positivity) (hp _ hr hr' hφ hφ')).imp_right (LE.le.trans · ?_)
    rw [show C*r^(-(d:ℝ)-e)*B*M=C*M*r^(-(d:ℝ)-e)*B by ring]
    grw [Real.rpow_le_rpow_of_exponent_ge hr (hr'.trans (min_le_left ..)) (show -(d:ℝ)-ε ≤ -(d:ℝ)-e by linarith [show e ≤ ε from min_le_left ..])];

lemma quoted_norm (s:ℝ)(hs:0<s)(φ:Trial E): Summable (fun i=>‖visit H s i φ‖):=by
   let q:=min 1 s; have hq:0<q:=lt_min zero_lt_one hs
   let ψ:=shrinking q⁻¹ φ
   have hψ: φ=shrinking q ψ:= by ext1 x; simp [ψ,shrinking_apply,shrink_apply,smul_smul,hq.ne',inv_pow]
   obtain ⟨R0,_hR',h'ψ⟩ := ψ.hasCompactSupport.isBounded.exists_pos_norm_le
   let R:=max 1 R0
   exact hψ.symm ▸ ((priced H s hs R (le_max_left ..) (show 0<(1:ℝ) by norm_num)).choose_spec.2 hq le_rfl (fun x hx=>mem_closedBall_zero_iff.mpr ((h'ψ x (subset_closure hx)).trans (le_max_right ..))) (Trial.majorant (d+1) ψ).choose_spec).1

def raw (H:Manage f d)(s:ℝ)(hs:0<s) : Trial E→ₗ[ℂ] ℂ where
   toFun φ:= ∑' i,visit H s i φ
   map_add' φ ψ:=by simp_rw [map_add]; exact Summable.tsum_add (summable_norm_iff.mp (quoted_norm H s hs φ)) (summable_norm_iff.mp (quoted_norm H s hs ψ))
   map_smul' c φ:=by simp_rw [map_smul,smul_eq_mul];exact tsum_mul_left
lemma raw_apply (s:ℝ)(hs:0<s)(φ:Trial E): raw H s hs φ=∑' i,visit H s i φ:=rfl
lemma raw_price (s:ℝ)(hs:0<s): Quoted s d (d+1) (raw H s hs):=by intro R hR e he; obtain ⟨C,hC,H'⟩:=priced H s hs R hR he; exact ⟨C,hC,fun _ hr hr' _ _ hx hy=> (H' hr hr' hx hy).2⟩

def numerical (H:Manage f d)(s:ℝ)(hs:0<s):Reading E:=Controlled.view (raw H s hs) (unscaled s hs (H.raw_price s hs))
lemma numerical_apply (s:ℝ)(hs:0<s)(φ:Trial E):(numerical H s hs) φ=∑' i:ℤ,visit H s i φ:=rfl
end Manage
end YM.Contacts
