import YM.SchemeRG11.Bubble.Meter

/-! Evaluate the T endpoint of the double-line loop. Use coordinates (T,t1/T), measure T dT dλ. -/
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.SchemeRG11.Bubble
open Function Set MeasureTheory Filter Metric Asymptotics Hot MSbar
open scoped ContDiff Topology
local notation "Tie" => ℝ×ℝ
variable {μ : ℝ} {w : ℝ→ℂ}

def route (w : ℝ→ℂ) := ∫ v in slab,w v
def scale (w : ℝ→ℂ) := ∫ v in slab, w v*braid v
section alone
variable {z : ℂ} (hw : Continuous w)
private lemma chosen {p : ℝ→ℂ} (h : Continuous p) : IntegrableOn p slab:= (h.continuousOn (s:=Icc 0 1) |>.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
include hw
lemma carrier_int {j : Bool} (hz : -1 < (phase j z).re) : IntegrableOn (carrier w j z) stem := by
  unfold IntegrableOn stem; rw [billets]; exact (intervalIntegral.intervalIntegrable_cpow' (a:=0) (b:=1) hz).1.mul_prod (chosen hw)
omit hw in
lemma charged {u : ℂ} (h : 0<u.re) :
    (∫ p in stem,(p.1:ℂ)^(u-1)*w p.2) = u⁻¹*route w := by
  unfold stem; rw [billets,integral_prod_mul (fun t : ℝ=> (t:ℂ)^(u-1)) w]
  have he : -1 < (u-1).re:= by simp only [Complex.sub_re,Complex.one_re]; linarith
  have hu : u≠0:=fun hr=> by rw [hr] at h; simp at h
  have hb:= integral_cpow (a:=0) (b:=1) (Or.inl he)
  rw [intervalIntegral.integral_of_le zero_le_one,Complex.ofReal_one,sub_add_cancel,Complex.one_cpow,Complex.ofReal_zero,Complex.zero_cpow hu, sub_zero,one_div] at hb
  rw [slab,hb]
  rfl
omit hw in
lemma true_phase (p : Tie) (hp : p∈stem) :
    carrier w true z p*halo p= (p.1:ℂ)^(z-1)*(w p.2*braid p.2) := by
  have ht : (p.1:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ((show 0<p.1 from hp.1.1).ne')
  simp only [halo,phase,index,carrier,Nat.cast_one,Complex.ofReal_mul]
  rw [Complex.cpow_sub (z-1) 1 ht,Complex.cpow_one]; field_simp

lemma remints {P : ℝ→ℂ} {D : ℂ} (j : Bool) (hz : (index j:ℕ) < z.re) :
    let f := fun p=> carrier w j z p*localTerms P D j (halo p);
    IntegrableOn f stem ∧ (∫ p in stem, f p)=
      if j then (z-1)⁻¹*route w*P 0 + z⁻¹*scale w*D else z⁻¹*route w*P 0 := by
  intro f
  have hh : -1<(phase j z).re:= by simp only [phase,Complex.sub_re,Complex.one_re,Complex.natCast_re]; linarith
  cases j
  · simp only [Bool.false_eq_true,↓reduceIte, f,localTerms, add_zero]
    refine ⟨(carrier_int hw hh).mul_const _,?_⟩
    rw [integral_mul_const]; congr 1; simp only [carrier,index,phase,Nat.cast_zero,sub_zero]
    exact charged (w:=w) (by simpa only [index,Nat.cast_zero] using hz)
  rw [if_pos rfl]
  let W : ℝ→ℂ := fun v=> w v*(braid v:ℂ)
  have hv: Continuous W := by unfold W braid; fun_prop
  let L (p : ℝ×ℝ) := carrier w true z p * P 0
  let U (p : ℝ×ℝ) := (carrier W false z p)*D
  have he : EqOn f (fun p=> L p+U p) stem := by
    intro p hp
    simp only [f, localTerms, ↓reduceIte,mul_add,←mul_assoc,true_phase (w:=w) (z:=z) p hp]
    simp only [L,U,carrier,phase,index,Nat.cast_zero,sub_zero,W]; ring
  have hA : IntegrableOn L stem := (carrier_int hw hh).mul_const _
  have ha:1<z.re:=by simpa only [index,Nat.cast_one] using hz
  have hx:0<z.re:=zero_lt_one.trans ha
  have hB : IntegrableOn U stem := (carrier_int hv (j:=false) (z:=z) (by simp only [index,phase,Complex.sub_re,Complex.one_re,Nat.cast_zero,sub_zero]; linarith)).mul_const D
  refine ⟨(hA.add hB).congr_fun he.symm stem_meas, ?_⟩
  rw [setIntegral_congr_fun stem_meas he,integral_add hA hB]
  dsimp only [L,U]; rw [integral_mul_const,integral_mul_const]
  have hc(z : ℂ) (h : 0<z.re) := charged (w:=w) h
  simp only [carrier,index,phase,Nat.cast_one,Nat.cast_zero,sub_zero]
  rw [hc (z-1) (by simp [ha]),charged (w:=W) hx]; rfl
end alone

def native (μ A B : ℝ) (w : ℝ→ℂ) (P : ℂ→ℝ→ℂ) (j : Bool) (e : ℂ) := Pole.factor μ e*(∫ p in stem ∪ foil A B,pouch w P j e p)

def restore (A B : ℝ) (w : ℝ→ℂ) (P : ℂ→ℝ→ℂ) (D : ℂ→ℂ) (j : Bool) (e : ℂ) := (∫ p in stem, purse w P D j e p)+(∫ p in foil A B,pouch w P j e p)
def extend (μ A B : ℝ) (w : ℝ→ℂ) (P : ℂ→ℝ→ℂ) (D : ℂ→ℂ) (j : Bool) (e : ℂ) :=
    Pole.factor μ e*(restore A B w P D j e+ if j then (e-1)⁻¹*route w*P e 0 + e⁻¹*scale w*D e else e⁻¹*route w*P e 0)

variable {w : ℝ→ℂ} (hw : Continuous w) {P : ℂ→ℝ→ℂ} {D : ℂ→ℂ} (h : Glaze P D) (j : Bool) {A B : ℝ} (hA : 1 ≤ A+B)
include hw h hA
theorem extends_conv {z : ℂ} (hz : (index j:ℕ) < z.re) :
    IntegrableOn (pouch w P j z) (stem ∪ foil A B) ∧ native μ A B w P j z=extend μ A B w P D j z := by
  have hx : -1<z.re:= lt_trans (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg _)) hz
  have hp:= pocket hw j h hx
  have hq := palm hw j h hA z
  let f := fun p=> carrier w j z p * localTerms (P z) (D z) j (halo p)
  obtain ⟨hi,hr⟩:= remints hw (P:=P z) (D:=D z) j hz
  have he : pouch w P j z=(fun p=> purse w P D j z p + f p) := by ext1 p; unfold pouch purse f; ring
  have ht : IntegrableOn (pouch w P j z) stem := he ▸ hp.add hi
  refine ⟨ht.union hq,?_⟩
  have hu : Disjoint stem (foil A B) := disjoint_left.mpr fun p hw hx=> not_le_of_gt (show 1<p.1 from hx.1) (show p.1≤1 from hw.1.2)
  have hT : (∫ p in stem,pouch w P j z p)=_ := (congrArg (fun h: Tie→ℂ=>∫ p in stem,h p) he).trans (integral_add hp hi)
  rw [native, extend,restore,setIntegral_union hu (foil_meas ..) ht hq,hT,hr]; ring

end YM.SchemeRG11.Bubble
