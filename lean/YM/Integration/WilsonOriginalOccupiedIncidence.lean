import YM.Integration.WilsonOriginalOccupiedOptical

/-! Restore all actual original test incidences together at their fixed-cardinality polynomial price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedIncidence
open Filter Finset Marker QuadraticLocal.Advent PhysicalNext.Repeat.Legato
open scoped Classical BigOperators

theorem toll {V:Type} [DecidableEq V] {J:Marker.Census V} (s:J.Mode) (n:ℕ) (load:s.val.card ≤ n)
    (w:V → ℝ)(wp:∀v,0<w v)(D M T B:ℝ)(dh:0 ≤ D)(dm:D ≤ M)(wpay:∀v,(w v)⁻¹ ≤ T)
    (bp:1 ≤ B)(gross:M*T ≤ B):
    D^s.val.card ≤ B^n*Poly.toll w s:=by
  have money:∀v,D ≤ B*w v:=by
    intro v
    have one:1 ≤ T*w v:=(inv_le_iff_one_le_mul₀ (wp v)).mp (wpay v)
    calc
      D ≤ M:=dm
      _ ≤ M*(T*w v):=le_mul_of_one_le_right (dh.trans dm) one
      _ = (M*T)*w v:=(mul_assoc ..).symm
      _ ≤ B*w v:=mul_le_mul_of_nonneg_right gross (wp v).le
  calc
    D^s.val.card = ∏_v∈s.val,D:=by simp
    _ ≤ ∏v∈s.val,B*w v:=prod_le_prod (fun _ _=>dh) (fun v _=>money v)
    _ = B^s.val.card*Poly.toll w s:=by simp [Poly.toll,prod_mul_distrib]
    _ ≤ B^n*Poly.toll w s:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ bp load) (Poly.worth wp s).le

private theorem budget (a u v:ℕ){β χ S:ℝ}(bp:1 ≤ β)(cp:0 ≤ χ)(pace:χ ≤ 2*β)
    (sp:0 ≤ S)(wallet:S ≤ β^a)(large:20*(2+(2:ℝ)^u*2^v) ≤ β):
    (10*χ)*(S*(χ+(2:ℝ)^u*χ^v)) ≤ β^(a+v+3):=by
  have b0:0 ≤ β:=zero_le_one.trans bp
  have cv:χ^v ≤ (2:ℝ)^v*β^v:=by simpa only [mul_pow] using pow_le_pow_left₀ cp pace v
  have below:β^v ≤ β^(v+1):=pow_le_pow_right₀ bp (Nat.le_succ _)
  have b1:β ≤ β^(v+1):=by simpa only [pow_one] using (pow_le_pow_right₀ bp (show 1 ≤ v+1 by omega))
  have sum:χ+(2:ℝ)^u*χ^v ≤ (2+(2:ℝ)^u*2^v)*β^(v+1):=by
    have left:=pace.trans (mul_le_mul_of_nonneg_left b1 (by norm_num:0 ≤ (2:ℝ)))
    have right:=mul_le_mul_of_nonneg_left (cv.trans (mul_le_mul_of_nonneg_left below (by positivity)))
      (by positivity:0 ≤ (2:ℝ)^u)
    linarith only [left,right]
  calc
    (10*χ)*(S*(χ+(2:ℝ)^u*χ^v)) ≤ (20*β)*(β^a*((2+(2:ℝ)^u*2^v)*β^(v+1))):=by
      exact mul_le_mul (by linarith only [pace]) (mul_le_mul wallet sum (by positivity) (by positivity))
        (by positivity) (by positivity)
    _ = (20*(2+(2:ℝ)^u*2^v))*β^(a+v+2):=by simp only [pow_add,pow_one,pow_two];ring
    _ ≤ β*β^(a+v+2):=mul_le_mul_of_nonneg_right large (pow_nonneg b0 _)
    _ = β^(a+v+3):=by exact (pow_succ' β (a+v+2)).symm

variable {G:Gauge} (R:Run G)(simple:G.Simple)
local notation "H" i:max => R.alloy.B.a.clock.hatBeta i

include simple in
theorem original (n a u v:ℕ):∀ᶠi:ℕ in atTop,
    ∀{V:Type} [DecidableEq V] {J:Marker.Census V} (s:J.Mode), s.val.card ≤ n →
    ∀(w:V → ℝ), (∀j,0<w j) → ∀{D S:ℝ}, 0 ≤ D → D ≤ 10*H (i+1) → 0 ≤ S → S ≤ (H i)^a →
    (∀j,(w j)⁻¹ ≤ S*(H (i+1)+(2:ℝ)^u*(H (i+1))^v)) →
      D^s.val.card ≤ (H i)^((a+v+3)*n)*Poly.toll w s:=by
  filter_upwards [(RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop (20*(2+(2:ℝ)^u*2^v)),
    RG01.Physical.nextHat simple R.alloy.B.a] with i wide pace V dec J s load w wp D S dp dm sp wallet wpay
  let power:ℝ:=(H i)^(a+v+3)
  have high:1 ≤ H i:=(R.alloy.B.a.fits.delayed _).le
  have high':0 ≤ H (i+1):=(R.alloy.B.a.fits.delayed _).le.trans' zero_le_one
  have paid:=budget a u v high high' pace sp wallet wide
  simpa only [power,←pow_mul] using toll s n load w wp D (10*H (i+1))
    (S*(H (i+1)+(2:ℝ)^u*(H (i+1))^v)) power dp dm wpay (one_le_pow₀ high) paid

end YM.Integration.WilsonOriginalOccupiedIncidence
