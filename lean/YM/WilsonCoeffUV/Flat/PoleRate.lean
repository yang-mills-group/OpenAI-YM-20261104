import YM.Extension.UV.FreeTail

/-!
# Wilson formal free supplies: pole-tail rates

This is real-cube control. No claim of such uniform pointwise control of massless
covariance on *complex* momenta! The rates are for the very train used in a
`Levels`. `m ≤ i ≤ n,n'`: compare tops n, n' with common depth at least i.
Track the one end cost at i (stage-dependent, absorb later), and separation in
M (ratio of spacings, not number of steps). No stationarity hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Set Function Filter Lattice RG Laurent Exterior Bloch Metric Next.Free Extension.UV.Linear
open scoped Topology BigOperators

lemma base_norm (p : Momentum) (hp : p ∈ baseCube) : ‖p‖ ≤ Real.pi := by
  apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2
  intro i
  have hh := hp.2 i
  have he := hp.1
  change star p=p at he
  have hh' := congr_fun he i
  have hz : (p i).im = 0 := by
    have h1 := congr_arg Complex.im hh'
    simp at h1
    linarith
  rw [show p i=((p i).re:ℂ) from Complex.ext rfl (by simpa using hz)]
  simpa using hh

lemma alias_lb {j} (v : Train j) (p : Momentum) (hp : p ∈ baseCube)
    (l : Site v.mass) : ‖p‖ / 4 / (v.mass.val:ℝ) ≤ ‖aliasAt p l‖ := by
  by_cases hh : l = 0
  · subst l
    rw [alias_zero_eq,narrow,norm_smul,norm_inv,Complex.norm_natCast,← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (by linarith [norm_nonneg p]) (side_pos _).le
  obtain ⟨a,ha⟩ := hit_grade l
  have hg := grade_gt hh
  have h := scaled_alias_lower l (mem_cube_real (base_subset_realCube zone_pos hp) zone_pos) a
    (by intro h; simp_all [up])
  rw [div_le_iff₀ (side_pos _),mul_comm ‖aliasAt p l‖]
  exact (calc
    ‖p‖ / 4 ≤ Real.pi / 4 := by gcongr; exact base_norm p hp
    _ ≤ (Real.pi / 4) * up l a := le_mul_of_one_le_right (by positivity) (up_ge ..)
    _ ≤ _ := h).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) (side_pos _).le)

/-- Bound the punctured covariance, gaining one power by paying only ONE
pure J price `Dcost` at ANY common finer level i. -/
theorem pole_tail (k : ℝ) (j : ℕ) (hj : 4 ≤ j) : ∃ C:ℝ, 0 < C ∧
    ∀ {G:Gauge} (A:Levels G) (m i n n' : ℕ), A.clock.J m = j → m ≤ i → i ≤ n → i ≤ n' →
    ∀ a p, p∈baseCube → p ≠ 0 →
      ‖Train.levelD k (location A n m) a p - Train.levelD k (location A n' m) a p‖ ≤
        C * (Dcost k (A.clock.J i) / (location A i m).mass.val) * ‖p‖⁻¹ := by
  obtain ⟨η,C,hη,hC,h⟩ := Train.feed_budget hj (fun i : Train j × Axis=> i.1) (fun i=> i.2)
  refine ⟨C*2*(Real.pi+4),by positivity,?_⟩
  intro G A m i n n' hJ hi hn hn' a p hp h0
  subst j
  let f := fun q=> Train.levelD k (location A n i) a q - Train.levelD k (location A n' i) a q
  set z : ℝ := ‖p‖; have hz : 0<z := norm_pos_iff.mpr h0
  let w := location A i m
  set M : ℝ := (w.mass.val:ℝ)
  set K := Dcost k (A.clock.J i)
  have hM : 1 ≤ M := by change 1 ≤ (w.mass.val:ℝ); exact_mod_cast w.mass.property
  have hm' : 0 < M := by linarith
  have hk : 0<K := Dcost_pos k _
  let B := 2*K*((Real.pi+4)*M/z)
  have h' (l:Site w.mass) : ‖f (aliasAt p l)‖ ≤ B := by
    have ha : z / 4 / M ≤ ‖aliasAt p l‖ := alias_lb w p hp l
    have hh : aliasAt p l ≠ 0 := norm_pos_iff.mp ((by positivity : 0 < z/4/M).trans_le ha)
    calc
      _ ≤ 2*K*(1+‖aliasAt p l‖⁻¹) := diff_bound k (A.clock.adm i) _ _ _ _ (alias_base hp l w.mass_odd) hh
      _ ≤ 2*K*(1+(z/4/M)⁻¹) := by gcongr
      _ ≤ B := by
        unfold B; gcongr 1
        rw [inv_div,div_div_eq_mul_div]; field_simp
        have H : z ≤ Real.pi := base_norm p hp
        nlinarith [Real.pi_pos]
  have hu : ‖feed w a (fun _=>1) p‖ ≤ C * (M^2)⁻¹ := (h (w,a)).bound p (mem_cube_real (base_subset_realCube hη hp) hη)
  rw [D_diff_tied k A a n n' i m hn hn' hi]
  apply (feed_control w a p hp.1 f h').trans
  apply (mul_le_mul_of_nonneg_right hu (show 0 ≤ B by unfold B; positivity)).trans
  apply le_of_eq; unfold B
  field_simp

variable {j : ℕ}

-- Normalize the pole using a scalar (the squared pi-sup norm on momentum).
def poleW (p : Momentum) : ℝ := ‖p‖^2
def smoothInv (k : ℝ) (v : Train j) (a : Axis) (p : Momentum) :=
    ((poleW p:ℂ)*v.levelD k a p)⁻¹
def qpart (a : Axis) (p : Momentum) := jewel 1 p a/(poleW p:ℂ)
def smoothDen (k : ℝ) (v : Train j) (p : Momentum) := ∑ a, qpart a p * smoothInv k v a p

lemma smoothInv_cap (k : ℝ) (hk : 0<k) (j : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ (v : Train j) a p, p∈baseCube → p≠0 → ‖smoothInv k v a p‖ ≤ C := by
  obtain ⟨η,c,hη,hc,H⟩ := Train.bulb_firm k hk (fun x : Train j × Axis => x.1) (fun x=> x.2)
  refine ⟨4 * meter.high^2 / c,by have := meter.high_pos; positivity,?_⟩
  intro v a p hp he
  have hx := H (v,a) p (base_subset_realCube hη hp)
  have hb : c ≤ ‖Train.bulb k v p a‖ := by simpa only [mul_one] using hx
  have hh := (divisor_real_bounds v.mass (base_subset_realCube zone_pos hp)).2
  have hh' : (divisor v.mass p).re = ‖divisor v.mass p‖ := (Silver.chipSq _ hp.1).norm.symm
  rw [hh'] at hh
  have hz := norm_pos_iff.mpr he
  have hv : 0 < poleW p := pow_pos hz _
  have hν : 0 < ‖divisor v.mass p‖ := norm_pos_iff.mpr (divisor_ne _ (base_subset_realCube zone_pos hp) he)
  rw [smoothInv,Train.D_bulb _ _ (base_subset_realCube zone_pos hp) he,norm_inv,norm_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  have hw : ‖divisor v.mass p‖ ≤ meter.high^2*(4*poleW p) := hh.trans (mul_le_mul_of_nonneg_left (length_bounds _).2 (sq_nonneg _))
  have hν' := hc.trans_le hb
  rw [← mul_div_assoc,inv_div]
  calc
    _ ≤ meter.high^2*(4*poleW p)/(poleW p*c) := by gcongr
    _ = _ := by field_simp

lemma qpart_bound (p : Momentum) (hp:p∈baseCube) (he : p≠0) (a) : ‖qpart a p‖ ≤ meter.high^2 := by
  have hw := mem_cube_real (base_subset_realCube zone_pos hp) zone_pos
  have hh := (seedQ_size 1 p hw a).2
  have ht := (seedQ_size 1 (-p) (cube_neg p hw) a).2
  have hu := meter.high_pos
  rw [Pi.neg_apply,norm_neg] at ht
  have hz : 0 < poleW p := pow_pos (norm_pos_iff.mpr he) _
  unfold qpart jewel
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz,div_le_iff₀ hz]
  calc
    _ ≤ (meter.high*‖p‖)*(meter.high*‖p‖) := mul_le_mul
      (hh.trans <| mul_le_mul_of_nonneg_left (norm_le_pi_norm p a) hu.le)
      (ht.trans <| mul_le_mul_of_nonneg_left (norm_le_pi_norm p a) hu.le)
      (norm_nonneg _) (by positivity)
    _ = _ := by unfold poleW; ring

lemma smoothDen_eq (p : Momentum) (v : Train j) k : smoothDen k v p = v.rho k p/((poleW p:ℂ)^2) := by
  unfold smoothDen smoothInv qpart Train.rho; rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_; simp only [div_eq_mul_inv,_root_.mul_inv_rev,← inv_pow]; ring

lemma smoothDen_cap (k : ℝ) (hk : 0<k) {j : ℕ} (hj : 4 ≤ j) : ∃ c:ℝ, 0<c ∧
    ∀ (v:Train j) p, p∈baseCube → p≠0 → c ≤ ‖smoothDen k v p‖ := by
  obtain ⟨η,c,hη,hc,H⟩ := Train.bend_firm k hk hj (id : Train j → Train j)
  have hl := meter.low_pos
  refine ⟨(meter.low^2)^2*c,by positivity,?_⟩
  intro v p hp he
  let Q := ‖Train.bend k v p‖
  have hh : c ≤ Q := by simpa only [Q,id,mul_one] using (H v p (base_subset_realCube hη hp))
  have hd := divisor_real_bounds v.mass (base_subset_realCube zone_pos hp)
  have ht := hd.1.trans (Complex.re_le_norm _)
  have hv := le_trans (a:=meter.low^2*poleW p)
    (mul_le_mul_of_nonneg_left (length_bounds p).1 (sq_nonneg _)) ht
  have hz : 0 < poleW p := pow_pos (norm_pos_iff.mpr he) _
  rw [smoothDen_eq,Train.recover_rho k hk v (base_subset_realCube zone_pos hp) he, norm_div,norm_mul,
      norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz]
  apply (le_div_iff₀ (pow_pos hz _)).2
  calc
    _ = (meter.low ^ 2 * poleW p)^2 * c := by ring
    _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (by positivity) hv _) hh hc.le (sq_nonneg _)

lemma punctured_pulse (v : Train j) (k : ℝ) (hk : 0<k) (p : Momentum) (hp : p∈baseCube) (he : p≠0) :
    pulse k v p = (smoothDen k v p)⁻¹ • mask 2 (fun a=> smoothInv k v a p) := by
  rw [pulse_sources k hk v (base_subset_realCube zone_pos hp) he,smoothDen_eq]
  have hh (a) : smoothInv k v a p = ((poleW p:ℂ))⁻¹ * (v.levelD k a p)⁻¹ := by simp [smoothInv,mul_comm]
  simp_rw [hh,mask_scale,smul_smul]
  have hv : (poleW p:ℂ)≠0 := by exact_mod_cast (pow_pos (norm_pos_iff.mpr he) 2).ne'
  rw [inv_div,div_eq_mul_inv, inv_pow, mul_right_comm (_^2), mul_inv_cancel₀ (pow_ne_zero 2 hv), one_mul]

lemma inv_sub_form (x y : ℂ) (hx : x≠0) (hy : y≠0) : ‖x⁻¹-y⁻¹‖ = ‖x⁻¹‖ * ‖y⁻¹‖ * ‖x-y‖ := by
  rw [show x⁻¹-y⁻¹=x⁻¹*y⁻¹*(y-x) by field_simp,norm_mul,norm_mul,norm_sub_rev]

/-- Use the bounded normalized inverses. No interpolation near the pole required. -/
theorem smoothInv_diff (k : ℝ) (hk : 0<k) (j : ℕ) (hj : 4 ≤ j) : ∃ C:ℝ, 0<C ∧
    ∀ {G:Gauge} (A:Levels G) (m i n n' : ℕ), A.clock.J m=j → m ≤ i → i ≤ n → i ≤ n' →
    ∀ a p, p∈baseCube → p≠0 →
      ‖smoothInv k (location A n m) a p - smoothInv k (location A n' m) a p‖ ≤
        C * (Dcost k (A.clock.J i)/(location A i m).mass.val) := by
  obtain ⟨c,hc,H⟩ := pole_tail k j hj
  obtain ⟨d,hd,T⟩ := smoothInv_cap k hk j
  refine ⟨d*d * (Real.pi*c),by positivity,?_⟩
  intro G A m i n n' hJ hi hn hn' a p hp h0
  subst j
  let R := location A n m; let R' := location A n' m
  set B := Dcost k (A.clock.J i)/(location A i m).mass.val
  have hb : 0 < B := div_pos (Dcost_pos ..) (side_pos _)
  let x : ℂ := (poleW p:ℂ)*R.levelD k a p
  let y : ℂ := (poleW p:ℂ)*R'.levelD k a p
  have hh := H A m i n n' rfl hi hn hn' a p hp h0
  have he := base_subset_realCube zone_pos hp
  have hp' := norm_pos_iff.mpr h0
  have hv := show 0<poleW p from pow_pos hp' _
  have hx : (poleW p:ℂ)≠0 := by exact_mod_cast hv.ne'
  have hm : ‖x-y‖ ≤ (Real.pi*c)*B := calc
    _ = poleW p * ‖Train.levelD k R a p - Train.levelD k R' a p‖ := by
      unfold x y; rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
    _ ≤ poleW p * (c * B * ‖p‖⁻¹) := by gcongr
    _ = ‖p‖*c*B := by unfold poleW; field_simp
    _ ≤ _ := by gcongr; exact base_norm p hp
  change ‖x⁻¹-y⁻¹‖ ≤ _
  rw [inv_sub_form _ _ (mul_ne_zero hx (Train.D_live k hk R he h0 _)) (mul_ne_zero hx (Train.D_live k hk R' he h0 _)), mul_assoc (d*d)];
  exact mul_le_mul (mul_le_mul (T _ a p hp h0) (T _ a p hp h0) (norm_nonneg _) hd.le) hm (norm_nonneg _) (by positivity)

lemma mul_est (x y z w : ℂ) {X Y Z W : ℝ} (a : ‖x-z‖ ≤ X) (b : ‖y‖ ≤ Y)
    (c : ‖z‖ ≤ Z) (d : ‖y-w‖ ≤ W) : ‖x*y-z*w‖ ≤ X*Y+Z*W := by
  rw [show x*y-z*w=(x-z)*y+z*(y-w) by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul]; exact add_le_add
    (mul_le_mul a b (norm_nonneg _) ((norm_nonneg _).trans a))
    (mul_le_mul c d (norm_nonneg _) ((norm_nonneg _).trans c))

/-- Symbol bound uniform all initial cutoffs, at EVERY real momentum. -/
theorem pulse_tail (k : ℝ) (hk : 0<k) (j : ℕ) (hj : 4 ≤ j) : ∃ C:ℝ, 0<C ∧
    ∀ {G:Gauge} (A:Levels G) (m i n n' : ℕ), A.clock.J m=j → m ≤ i → i ≤ n → i ≤ n' →
    ∀ a b p, p∈baseCube →
      ‖pulse k (location A n m) p a b - pulse k (location A n' m) p a b‖ ≤
        C * (Dcost k (A.clock.J i)/(location A i m).mass.val) := by
  obtain ⟨c,hc,h⟩ := smoothInv_cap k hk j
  obtain ⟨d,hd,g⟩ := smoothDen_cap k hk hj
  obtain ⟨B,hB,H⟩ := smoothInv_diff k hk j hj
  set q := meter.high^2; have hq := pow_pos meter.high_pos 2
  set C := (d⁻¹*d⁻¹*(4*q*B))*(c*c)+d⁻¹*(B*c+c*B)
  refine ⟨C,by unfold C q; positivity,?_⟩
  intro G A m i n n' hJ hi hn hn' a b p hp
  subst j
  set x := Dcost k (A.clock.J i)/(location A i m).mass.val
  have hx : 0 < x := div_pos (Dcost_pos ..) (side_pos _)
  have hc' : 0 ≤ C*x := mul_nonneg (by unfold C q; positivity) hx.le
  by_cases he : p=0
  · rw [he]; simpa using hc'
  let v := location A n m; let w := location A n' m
  have hs y : ‖smoothInv k v y p - smoothInv k w y p‖ ≤ B*x := H A m i n n' rfl hi hn hn' y p hp he
  have hm : ‖smoothDen k v p-smoothDen k w p‖ ≤ 4*q*B*x := by
    unfold smoothDen; rw [← Finset.sum_sub_distrib]; simp_rw [← mul_sub]; apply (norm_sum_le ..).trans
    apply le_trans (b:=∑ _ : Axis, q*(B*x))
    · exact Finset.sum_le_sum fun y _ => by rw [norm_mul]; exact mul_le_mul (qpart_bound p hp he y) (hs y) (norm_nonneg _) hq.le
    simp [Axis]; apply le_of_eq; ring
  have hz (u : Train (A.clock.J m)) : smoothDen k u p≠0 := norm_pos_iff.mp (hd.trans_le (g u p hp he))
  have hv (u : Train (A.clock.J m)) : ‖(smoothDen k u p)⁻¹‖ ≤ d⁻¹ := by rw [norm_inv]; gcongr; exact g u p hp he
  have ho : ‖(smoothDen k v p)⁻¹-(smoothDen k w p)⁻¹‖ ≤ d⁻¹*d⁻¹*(4*q*B*x) := by
    rw [inv_sub_form _ _ (hz _) (hz _)]; gcongr <;> exact hv _
  rw [punctured_pulse _ k hk p hp he,punctured_pulse _ k hk p hp he]
  simp only [mask,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul]
  split_ifs with h'
  · obtain ⟨r,s,hrs,ha⟩ := Finset.card_eq_two.mp a.property
    let S (t : Train (A.clock.J m)) (z : Axis) := smoothInv k t z p
    simp only [inventory, ha, Finset.prod_insert (Finset.notMem_singleton.mpr hrs), Finset.prod_singleton]
    have ht : ‖S v r * S v s‖ ≤ c*c := by rw [norm_mul]; gcongr <;> exact h _ _ p hp he
    have hy := mul_est (S v r) (S v s) (S w r) (S w s) (hs r) (h _ _ p hp he) (h _ _ p hp he) (hs s)
    -- distribute common x
    exact (mul_est _ _ _ _ ho ht (hv w) hy).trans_eq (by unfold C; ring)
  simpa using hc'

end YM.WilsonCoeffUV
