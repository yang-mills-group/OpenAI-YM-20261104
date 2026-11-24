import YM.SchemeRG11.Cluster.Wedge

/-! Independent tripod with dimensions varying. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.SchemeRG11.Cluster
open Set MeasureTheory Filter Metric Function Hot MSbar
open scoped Topology ContDiff BigOperators
variable {n : ℕ}

lemma credit {K : Set (Nodes n)} (hk : IsCompact K) (hx : K ⊆ clearance n) : ∃ d>0, ∀ x∈K, ∀ i, d≤bevel i x := by
  by_cases he: K.Nonempty
  · choose b hb he using fun i=> hk.exists_isMinOn he ((bevel_c i).continuous.continuousOn)
    obtain ⟨i,-,hi⟩:=Finset.exists_min_image Finset.univ (fun i=> bevel i (b i)) Finset.univ_nonempty
    exact ⟨_, (hx (hb i)) i,fun x hx j=> (hi j (Finset.mem_univ _)).trans (he j hx)⟩
  exact ⟨1,zero_lt_one,fun x hx=> (he ⟨x,hx⟩).elim⟩

def wages (p : Time) := (due p.1*due p.2.1*due p.2.2)
lemma wag (p : Time) (hp : p∈tripod) : 0<wages p := mul_pos (mul_pos (dues hp.1) (dues hp.2.1)) (dues hp.2.2)
lemma compass : IntegrableOn (fun p=> (wages p)⁻¹) tripod := by
  have hi : IntegrableOn (fun t => (due t)⁻¹) openZen := by
    have hh:= integrable_one_add_norm (μ:=(volume:Measure ℝ)) (by norm_num : (Module.finrank ℝ ℝ:ℝ)<4/3)
    refine hh.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro t ht; have ht:0<t:=ht
    change (1+‖t‖)^(-(4/3:ℝ))=(due t)⁻¹; rw [Real.rpow_neg (by positivity),due,Real.norm_of_nonneg ht.le]
  unfold IntegrableOn tripod
  rw [show (volume: Measure Time)=Measure.prod volume volume from rfl,←Measure.prod_restrict,show (volume:Measure (ℝ×ℝ))=Measure.prod volume volume from rfl,←Measure.prod_restrict]
  convert! hi.mul_prod (hi.mul_prod hi) using 1
  ext p; unfold wages; ring

private lemma little {b c : ℝ} (h:0<b) (hv:b≤c) (k:b≤1) : c⁻¹^2*due c ≤ 4*b⁻¹^2 := by
  have hp:= lt_of_lt_of_le h hv
  rcases le_total c 1 with t|t
  · grw [flakes hp t,←hv]; exact le_of_eq (mul_comm ..)
  grw [dries t]
  field_simp; nlinarith

variable {μ : ℝ} (hμ : 0<μ) {K : Set (Nodes n)} (hk : IsCompact K) (hx : K⊆clearance n)
include hμ hk hx
theorem respite (l : Sweep n) : ∃ C>0, ∀ p∈tripod, ∀ x∈K, ‖spin μ l p 0 x‖ ≤ C/wages p := by
  obtain ⟨d,hd,h⟩:= credit hk hx
  obtain ⟨P,hp⟩:= plugs hμ l
  obtain ⟨C,hC,k,hP⟩:= Tint.top P (isCompact_singleton (x:=(0:ℂ))) hk
  obtain ⟨D,hD,H⟩:= Hot.rain (by positivity : 0<d/3) (k+4)
  refine ⟨max (16*C) (C*64*D),by positivity, fun p he x hz=> (le_div_iff₀ (wag p he)).mpr ?_⟩
  obtain ⟨a,b,c,f⟩:=sorted p he
  have ha:=f.pos; have hb:=lt_of_lt_of_le ha f.floor
  have hc:=lt_of_lt_of_le hb f.ceil
  have ht:=globe p he
  obtain ⟨hr,hh⟩:=f.shades hd (h x hz)
  have hu:=dues ha; have hv:=dues hb; have hw:=dues hc
  rw [hp,wages,← f.pays, strength _ _ ht,Complex.zero_re,zero_sub,Real.rpow_neg ht.le,Real.rpow_two,← inv_pow]
  grw [← f.lo,← hh]
  rw [← neg_mul]
  rcases le_total b 1 with hy|hy
  · refine le_trans ?_ (le_max_right ..)
    grw [hP 0 rfl x hz b⁻¹ ((one_le_inv₀ hb).mpr hy) _ hr, flakes ha (f.floor.trans hy), flakes hb hy]
    let E := Real.exp (-(d/3)*b⁻¹)
    calc _ = C*16*(b⁻¹)^(k+2)*E*((c⁻¹)^2*due c) := by unfold E; ring
         _ ≤ C*16*b⁻¹^(k+2)*E*(4*b⁻¹^2) := mul_le_mul_of_nonneg_left (little hb f.ceil hy) (by unfold E; positivity)
         _ = C*64*(b⁻¹^(k+4)*E) := by ring
         _ ≤ C*64*D := mul_le_mul_of_nonneg_left (H b⁻¹ (by positivity)) (by positivity)
  refine le_trans ?_ (le_max_left ..)
  grw [hP 0 rfl x hz 1 le_rfl _ (fun i=> (hr i).trans ((inv_le_one₀ hb).mpr hy)), Real.exp_le_one_iff.mpr (by rw [neg_mul]; exact neg_nonpos.mpr (by positivity) : -(d/3)*b⁻¹ ≤ 0),raise ha f.floor,wealth hy f.ceil]
  rw [one_pow,mul_one,mul_one]; field_simp; linarith

theorem flash (l : Sweep n) {U : Set ℂ} (hc : IsCompact U) (R : ℝ) :
    ∃ C>0, ∀ x∈K, ∀ e∈U, ∀ p∈tripod, knot p ≤ R → ‖spin μ l p e x‖ ≤ C := by
  obtain ⟨d,hd,h⟩:= credit hk hx
  obtain ⟨P,hp⟩:= plugs hμ l
  obtain ⟨C,hC,k,hP⟩:= Tint.top P hc hk
  obtain ⟨m,hm⟩:=enough hc
  obtain ⟨D,hD,H⟩:= Hot.rain (by positivity : 0<d/3) (k+2*m)
  let Z:= (1+|R|)^m
  have hhZ : 1≤Z:=one_le_pow₀ (by linarith [abs_nonneg R])
  refine ⟨Z*C*(1+D),by unfold Z; positivity, fun x hx e he p ha hR=>?_⟩
  obtain ⟨a,b,c,f⟩:=sorted p ha
  have hb:=lt_of_lt_of_le f.pos f.floor
  have ht:=globe p ha
  obtain ⟨hr,hh⟩:=f.shades hd (h x hx)
  rw [hp,strength _ _ ht]
  have hv : b*b ≤ knot p := (mul_le_mul_of_nonneg_left f.ceil hb.le).trans f.lo
  have hu (h : 1 ≤ knot p) : (knot p)^(e.re-2) ≤ Z := by
     grw [Real.rpow_le_rpow_of_exponent_le h (hm _ he).2]; unfold Z; rw [Real.rpow_natCast]; gcongr; linarith [le_abs_self R]
  grw [← hh]; rw [← neg_mul]
  rcases le_total b 1 with hy|hy
  · have hW : (knot p)^(e.re-2) ≤ Z*b⁻¹^(2*m) := by
       have hw := (one_le_inv₀ hb).mpr hy
       rcases le_total 1 (knot p) with ho|ho
       · exact (hu ho).trans (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hw))
       grw [Real.rpow_le_rpow_of_exponent_ge ht ho (hm _ he).1]
       rw [Real.rpow_neg_natCast,zpow_neg,zpow_natCast,← inv_pow]
       grw [←hv]; exact le_trans (le_of_eq (by rw [pow_mul]; ring : _=b⁻¹^(2*m))) (le_mul_of_one_le_left (by positivity) hhZ)
    grw [hW,hP e he x hx b⁻¹ ((one_le_inv₀ hb).mpr hy) _ hr]
    calc _ = Z*C*(b⁻¹^(k+2*m)*Real.exp (-(d/3)*b⁻¹)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left ((H b⁻¹ (by positivity)).trans (by linarith)) (by unfold Z; positivity)
  have hp :1 ≤ knot p := hv.trans' (one_le_mul_of_one_le_of_one_le hy hy)
  grw [hP e he x hx 1 le_rfl _ (fun i=> (hr i).trans ((inv_le_one₀ hb).mpr hy)), Real.exp_le_one_iff.mpr (by rw [neg_mul]; exact neg_nonpos.mpr (by positivity) : -(d/3)*b⁻¹ ≤ 0),hu hp]
  rw [one_pow,mul_one,mul_one]; exact le_mul_of_one_le_right (by unfold Z; positivity) (by linarith)
end YM.SchemeRG11.Cluster
