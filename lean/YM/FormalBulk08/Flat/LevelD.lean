import YM.FormalBulk08.Flat.High

/-!
Real-momentum rate for the massless covariance ingredient of the actual
linear history. Includes noise. None of the comparison arguments here
extrapolate derivatives of a nonlinear cutoff limit. We do not need D
itself at p=0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Precision RG Next.Free UVExtension.Free
open scoped Topology BigOperators
variable {G : Gauge}

lemma nozzle_snoc (A : Levels G) (i d : ℕ) :
    (flying A (d+1) i).nozzle=(flying A d i).nozzle++[flying A d i] := by
  induction d generalizing i with
  | zero => rfl
  | succ d h =>
    let P : Train (A.clock.J (i+1))→Train (A.clock.J i) := Train.hop (j:=A.clock.J i) (A.clock.op i 0).patch (A.fits.mono (Nat.le_succ i)) (A.fits.stepSlow i)
    change .top _ :: ((flying A (d+1) (i+1)).nozzle.map P) = (.top _ :: ((flying A d (i+1)).nozzle.map P)) ++ [P (flying A d (i+1))]
    rw [h]; simp only [List.map_append,List.map_cons,List.map_nil,List.cons_append]

lemma noise_real_rate (j : ℕ) (hj : 4≤j) : ∃ C : ℝ, 0<C ∧ ∀ (A : Levels G) (i d D : ℕ) (p : Momentum)
    (a : Axis), A.clock.J i=j → p∈baseCube → d≤D →
    ‖(flying A d i).levelNoise a p-(flying A D i).levelNoise a p‖ ≤
      C*(Real.sqrt (A.S.steps i d).val)⁻¹ := by
  obtain ⟨σ,C,hσ,hC,h⟩ := Train.feed_budget hj (fun x : Train j × Axis=>x.1) (fun x=>x.2)
  refine ⟨3*C,by positivity,fun A i d D p a ha hp he=>?_⟩
  subst j
  induction he using Nat.decreasingInduction with
  | self => simp only [sub_self,norm_zero]; positivity
  | of_succ d hd ih =>
    let f l:= (flying A l i).levelNoise a p
    let m:= A.S.steps i d
    have hm : 1≤(m.val:ℝ) := by exact_mod_cast m.property
    have h' := ((h (flying A d i,a)).bound p (mem_cube_real (base_subset_realCube hσ hp) hσ))
    change ‖feed _ _ _ p‖ ≤ C*((((flying A d i).mass.val:ℝ)^2)⁻¹) at h'
    have hh : ‖f d-f (d+1)‖ ≤ C*(Real.sqrt m.val)⁻¹ := by
      unfold f Train.levelNoise; rw [nozzle_snoc]; unfold Train.stream; rw [List.map_append,List.sum_append]; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,← sub_sub,sub_self,zero_sub,norm_neg]
      rw [flying_mass] at h'
      apply h'.trans (mul_le_mul_of_nonneg_left _ hC.le)
      exact (inv_le_inv₀ (pow_pos (side_pos m) _) (Real.sqrt_pos.mpr (side_pos m))).2 ((sqrt_mass m).2.trans (le_self_pow₀ hm (by decide)))
    refine (norm_sub_le_norm_sub_add_norm_sub (f d) (f (d+1)) (f D)).trans ((add_le_add hh ih).trans ?_)
    have hx := mul_le_mul_of_nonneg_left (sqrt_gain A.S i d) (show 0≤3*C by positivity)
    unfold m; linarith only [hx]

lemma box_price (p : Momentum) (hp : p∈baseCube) : ‖p‖ ≤ domainRadius :=
  (pi_norm_le_iff_of_nonneg domainRadius_pos.le).mpr (fun i=>zone_in_disk p (mem_cube_real (base_subset_realCube zone_pos hp) zone_pos) i)

lemma divisor_rate (A : Levels G) (i d D) (p : Momentum) (hp : p∈baseCube) (h : d≤D) :
    ‖divisor (A.S.steps i d) p-divisor (A.S.steps i D) p‖ ≤
      32*‖p‖^2*domainRadius*(Real.sqrt (A.S.steps i d).val)⁻¹ := by
  apply (divisor_difference _ _ (steps_incr A.S d D h i) p hp.1).trans
  have hL := domainRadius_pos; let m:=A.S.steps i d
  have he : 0<Real.sqrt (m.val:ℝ) := Real.sqrt_pos.mpr (side_pos m)
  calc
    _ = (32*‖p‖^2*‖p‖)/(m.val:ℝ) := by unfold m; ring
    _ ≤ (32*‖p‖^2*domainRadius)/Real.sqrt (m.val:ℝ) := div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left (box_price _ hp) (by positivity)) he (sqrt_mass m).2
    _ = _ := div_eq_mul_inv ..

lemma lid_real_rate (A : Levels G) (a : Axis) (i d D : ℕ) (p : Momentum) (hp : p∈baseCube) (he : d≤D) :
    ‖(flying A d i).lid a p-(flying A D i).lid a p‖ ≤
      6*driveCost (A.clock.J i)*domainRadius * (Real.sqrt (A.S.steps i d).val)⁻¹ := by
  unfold Train.lid yen; rw [flying_mass,flying_mass,← narrow_neg,← narrow_neg]
  have hh := drive_rate A a i d D p hp.1 he
  have hx := drive_rate A a i d D (-p) (physical_minus p hp.1) he
  apply (product_move _ _ _ _ hh hx (drive_unit A _ _ _ p hp.1) (drive_unit A _ _ _ (-p) (physical_minus p hp.1))).trans
  rw [norm_neg]; have := driveCost_pos (A.clock.J i)
  calc
    _ = 6*driveCost (A.clock.J i)*‖p‖*(Real.sqrt (A.S.steps i d).val)⁻¹ := by ring
    _ ≤ _ := by gcongr; exact box_price _ hp

lemma drain_guard (k : ℝ) (j : ℕ) (hj : 4≤j) : ∃ C : ℝ, 0<C ∧ ∀ (V : Train j) (p : Momentum),
    p∈baseCube → ∀ a : Axis, ‖V.drain k a p‖ ≤ C := by
  obtain ⟨σ,C,hσ,hC,h⟩:= Train.drain_reserve k hj (fun x:Train j×Axis=>x.1) (fun x=>x.2)
  exact ⟨C,hC,fun V p hp a=> ((h (V,a)).bound p (mem_cube_real (base_subset_realCube hσ hp) hσ)).trans_eq (mul_one _)⟩
lemma drain_real_rate (k : ℝ) (j : ℕ) (hj : 4 ≤ j) : ∃ C : ℝ, 0<C ∧ ∀ (A : Levels G) (i d D : ℕ) (p : Momentum)
    (a : Axis), A.clock.J i=j → p∈baseCube → d≤D →
    ‖(flying A d i).drain k a p-(flying A D i).drain k a p‖ ≤ C*(Real.sqrt (A.S.steps i d).val)⁻¹ := by
  obtain ⟨E,hE,he⟩ := noise_real_rate (G:=G) _ hj
  obtain ⟨H,hH,h⟩ := high_rate (G:=G) j
  refine ⟨H+‖(k:ℂ)⁻¹‖*E,by positivity,fun A i d D p a hj hp ht=>?_⟩
  unfold Train.drain; rw [add_sub_add_comm,← mul_sub]
  refine (norm_add_le ..).trans ?_
  rw [norm_mul]
  exact (add_le_add (h _ _ _ _ _ _ hj hp ht) (mul_le_mul_of_nonneg_left (he _ _ _ _ _ _ hj hp ht) (norm_nonneg _))).trans_eq (by ring)

lemma bulb_caps (j : ℕ) (hj : 4≤j) (k : ℝ) (hk : 0<k) : ∃ c C : ℝ, 0<c ∧
    ∀ (V : Train j) (p : Momentum), p∈baseCube → ∀ a : Axis, c ≤ ‖V.bulb k p a‖ ∧ ‖V.bulb k p a‖ ≤ C := by
  obtain ⟨σ,C,hσ,_,h⟩:= Train.bulb_budget k hj (fun x:Train j×Axis=>x.1) (fun x=>x.2)
  obtain ⟨η,c,hη,hc,hh⟩:= Train.bulb_firm k hk (fun x:Train j×Axis=>x.1) (fun x=>x.2)
  exact ⟨c,C,hc,fun V p hp a=> ⟨(mul_one c).symm.trans_le (hh (V,a) p (base_subset_realCube hη hp)), ((h (V,a)).bound p (mem_cube_real (base_subset_realCube hσ hp) hσ)).trans_eq (mul_one _)⟩⟩
lemma divisor_cap : ∃ C : ℝ, 0<C ∧ ∀ M : Side, ∀ p ∈ baseCube, ‖divisor M p‖ ≤ C := by
  obtain ⟨σ,C,hσ,hC,h⟩:= divisor_control (fun M : Side=>M)
  exact ⟨C,hC,fun V p hp=> ((h V).bound p (mem_cube_real (base_subset_realCube hσ hp) hσ)).trans_eq (mul_one _)⟩
lemma bulb_real_rate (j : ℕ) (hj : 4≤j) (k : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ (A : Levels G) (i d D : ℕ) (p : Momentum)
      (a : Axis), A.clock.J i=j → p∈baseCube → d≤D →
      ‖(flying A d i).bulb k p a-(flying A D i).bulb k p a‖ ≤ C*(Real.sqrt (A.S.steps i d).val)⁻¹ := by
  obtain ⟨C,hC,h⟩:=drain_real_rate (G:=G) k j hj
  obtain ⟨K,hK,H⟩:=drain_guard k j hj
  obtain ⟨M,hM,hS⟩:=divisor_cap
  have hP:=driveCost_pos j; have hx:=domainRadius_pos
  refine ⟨6*driveCost j*domainRadius+M*C+32*domainRadius^3*K,by positivity,fun A i d D p a ha hp hD=>?_⟩
  subst j
  have ht := lid_real_rate A a i d D p hp hD
  unfold Train.bulb; rw [add_sub_add_comm,flying_mass,flying_mass]
  refine (norm_add_le ..).trans ((add_le_add ht
    (product_move _ _ _ _ (divisor_rate A i d D p hp hD) (h A i d D p a rfl hp hD) (hS _ p hp) (H _ p hp a))).trans ?_)
  let I:= (Real.sqrt (A.S.steps i d).val)⁻¹
  have hw : ‖p‖^2*domainRadius*I*K ≤ domainRadius^3*I*K := by
    nth_rw 1 [pow_succ domainRadius 2]; gcongr; exact box_price _ hp
  unfold I at hw; linarith only [hw]

/-- Real cube, massless singular order. Constant determined before all L. -/
theorem levelD_rate (j : ℕ) (hj : 4≤j) (k : ℝ) (hk : 0<k) :
    ∃ C : ℝ, 0<C ∧ ∀ (A : Levels G) (i N N' : ℕ) (p : Momentum) (a : Axis),
      A.clock.J i=j → p∈baseCube → p≠0 → i≤N → N≤N' →
        ‖(location A N i).levelD k a p-(location A N' i).levelD k a p‖ ≤
          C*(Real.sqrt (A.S.steps i (N-i)).val)⁻¹ / ‖p‖^2 := by
  obtain ⟨C,hC,H⟩:=bulb_real_rate (G:=G) j hj k
  obtain ⟨c,E,hc,h⟩:=bulb_caps j hj k hk
  let U:=meter.low^2; have hU:0<U:=pow_pos meter.low_pos _
  let D:=32*domainRadius; have hD:0<D:=mul_pos (by norm_num) domainRadius_pos
  have hE : 0<E:= hc.trans_le ((h (.top _) 0 (by
    constructor <;> simp [physical,Real.pi_pos.le]) 0).1.trans (h (.top _) 0 (by
    constructor <;> simp [physical,Real.pi_pos.le]) 0).2)
  refine ⟨E*(D/(U*U))+C/U,by positivity,fun A i N M p a hi hp hn _ hM=>?_⟩
  subst j
  have hv:= norm_pos_iff.mpr hn; have he := base_subset_realCube zone_pos hp
  rw [Train.D_bulb k _ he hn,Train.D_bulb k _ he hn]; nth_rw 1 [div_eq_mul_inv]; nth_rw 1 [div_eq_mul_inv]
  let L:=(A.S.steps i (N-i)); let L':=(A.S.steps i (M-i))
  let I:=(Real.sqrt L.val)⁻¹
  have hh : N-i≤M-i := by omega
  have hx : 0<U*‖p‖^2:=mul_pos hU (pow_pos hv _)
  unfold location; rw [flying_mass,flying_mass]; apply (product_move _ _ _ _
    (H A i (N-i) (M-i) p a rfl hp hh) (inv_move hx hx (pole_floor p hp _) (pole_floor p hp _) (divisor_rate A i _ _ p hp hh))
    (h _ p hp a).2 (show ‖(divisor L' p)⁻¹‖≤ (U*‖p‖^2)⁻¹ from ?_)).trans
  · refine le_of_eq ?_
    unfold D
    field_simp
  rw [norm_inv]; have ht := pole_floor p hp L'
  exact (inv_le_inv₀ (hx.trans_le ht) hx).mpr ht

theorem levelD_caps (j : ℕ) (hj : 4≤j) (k : ℝ) (hk : 0<k) :
    ∃ c C : ℝ, 0<c ∧ ∀ (V : Train j) (p : Momentum) (a : Axis), p∈baseCube → p≠0 →
    c ≤ ‖V.levelD k a p‖ ∧ ‖V.levelD k a p‖ ≤ C / ‖p‖^2 := by
  obtain ⟨c,E,hc,h⟩:=bulb_caps j hj k hk
  obtain ⟨C,hC,H⟩:=divisor_cap
  refine ⟨c/C,E/meter.low^2,by positivity,fun V p a hp he=> ?_⟩
  have ht := pole_floor p hp V.mass
  have hh := h V p hp a
  have hh' := hc.trans_le hh.1
  have hd := H V.mass p hp
  have hv : 0 < meter.low^2*‖p‖^2 := mul_pos (pow_pos meter.low_pos _) (pow_pos (norm_pos_iff.mpr he) _)
  rw [Train.D_bulb k V (base_subset_realCube zone_pos hp) he,norm_div]
  exact ⟨div_le_div₀ hh'.le hh.1 (hv.trans_le ht) hd, (div_le_div₀ (hh'.trans_le hh.2).le hh.2 hv ht).trans_eq (div_div ..).symm⟩

lemma bend_floor (j : ℕ) (hj : 4≤j) (k : ℝ) (hk : 0<k) :
    ∃ c : ℝ, 0<c ∧ ∀ V : Train j, ∀ p ∈ baseCube, c ≤ ‖V.bend k p‖ := by
  obtain ⟨η,c,hη,hc,h⟩:= Train.bend_firm k hk hj (fun x:Train j=>x)
  exact ⟨c,hc,fun V p hp=>(mul_one c).symm.trans_le (h V p (base_subset_realCube hη hp))⟩
lemma rho_real_floor (j : ℕ) (hj : 4≤j) (k : ℝ) (hk : 0<k) :
    ∃ c : ℝ, 0<c ∧ ∀ V : Train j, ∀ p ∈ baseCube, p≠0 → c*‖p‖^4≤‖V.rho k p‖ := by
  obtain ⟨c,hc,h⟩:=bend_floor j hj k hk
  refine ⟨meter.low^4*c,mul_pos (pow_pos meter.low_pos _) hc,fun V p hp he=>?_⟩
  rw [Train.recover_rho k hk V (base_subset_realCube zone_pos hp) he,norm_mul,norm_pow]
  refine le_trans ?_ (mul_le_mul (pow_le_pow_left₀ (show 0≤meter.low^2*‖p‖^2 by positivity) (pole_floor _ hp _) 2) (h _ _ hp) hc.le (by positivity))
  exact le_of_eq (by ring)
end YM.FormalBulk08.Flat
