import YM.PhysMS.Frame.Step

/-! The reciprocal engineering cost of an arbitrary far detector is sharp up to an
arbitrarily small power.  Its two frames belong to the same measured continuum state.
The ultraviolet threshold works before both the separation ratio and the physical field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFrame
open Filter Set Spec Climb Trace.Pilot PhysMS
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {q : Extraction.Order} {S : Table C.book}

private theorem engineering (d : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 1 ≤ T → ∀ v : (Bel C.book).Field d,
      ‖Pert.Scale.gear C.labels d T v‖ ≤ M * T^d * ‖v‖ := by
  let B := Extra.FD.recorded C.labels d
  let c i := ‖B.b i‖ * ‖(B.b.coord i).toContinuousLinearMap‖
  refine ⟨∑ i, c i, Finset.sum_nonneg (fun i _ => by unfold c; positivity), ?_⟩
  intro T hT v
  rw [Finset.sum_mul, Finset.sum_mul]
  nth_rw 1 [← B.b.sum_repr v]
  rw [map_sum]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => ?_)
  have h₀ := zero_le_one.trans hT
  rw [map_smul, Pert.Scale.rare, norm_smul, norm_smul, Complex.norm_pow,
    Complex.norm_real, Real.norm_of_nonneg h₀]
  change ‖B.b.coord i v‖ * (T^(B.w i).1 * ‖B.b i‖) ≤ c i * T^d * ‖v‖
  refine (mul_le_mul ((B.b.coord i).toContinuousLinearMap.le_opNorm v)
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT (B.cap i)) (norm_nonneg _))
    (by positivity) (by positivity)).trans_eq ?_
  unfold c
  ring

private theorem reflected_step (F : Final C q S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ c : ℝ, 0 < c → ∀ᶠ r in trail, ∀ t ∈ Icc c 1, ∀ x : S.Field d,
      ‖(J (t*r) d).symm x‖ ≤ K * t^(-(d:ℝ)) * ‖(J r d).symm x‖ := by
  obtain ⟨A,hA,h⟩ := Frame.comparison F d J H
  obtain ⟨M,_,hM⟩ := engineering (C:=C) d
  refine ⟨max 1 (A*M), le_max_left .., fun c hc => ?_⟩
  filter_upwards [h c hc] with r hr t ht x
  have hp := hc.trans_le ht.1
  let b := Frame.cocycle d J r t hp
  let u := (J (t*r) d).symm x
  let v := (J r d).symm x
  have hscale : Pert.Scale.gear C.labels d t (b u) = v := by
    apply (J r d).injective
    rw [show J r d _ = J (t*r) d u from Frame.cocycle_value d J u t r hp]
    simp [u,v]
  have hchange : b u = Pert.Scale.gear C.labels d t⁻¹ v := by
    rw [← hscale,Pert.Scale.gear_inverse C.labels hp.ne']
  have him : t⁻¹^d = t^(-(d:ℝ)) := by rw [Real.rpow_neg hp.le,Real.rpow_natCast,inv_pow]
  change ‖u‖ ≤ _ * t^(-(d:ℝ)) * ‖v‖
  calc
    ‖u‖ = ‖b.symm (Pert.Scale.gear C.labels d t⁻¹ v)‖ := by rw [← hchange,b.symm_apply_apply]
    _ ≤ A * ‖Pert.Scale.gear C.labels d t⁻¹ v‖ := (hr t ht).2 _
    _ ≤ A * (M * t⁻¹^d * ‖v‖) := mul_le_mul_of_nonneg_left (hM _ ((one_le_inv₀ hp).mpr ht.2) _) (zero_le_one.trans hA)
    _ = (A*M) * t^(-(d:ℝ)) * ‖v‖ := by rw [him]; ring
    _ ≤ _ := by gcongr; exact le_max_right ..

/-- At every sufficiently small outer radius, the near coordinates of every actual physical
field are controllable simultaneously down to arbitrarily small inner/outer ratios. -/
theorem between (F : Final C q S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, ∀ t ∈ Ioc (0:ℝ) 1, ∀ x : S.Field d,
      ‖(J (t*r) d).symm x‖ ≤ K * t^(-(d:ℝ)-ε) * ‖(J r d).symm x‖ := by
  obtain ⟨K,hK,step⟩ := reflected_step F d J H
  obtain ⟨c,hc₀,hc,hbuy⟩ := ((show ∀ᶠ c : ℝ in trail, 0 < c from self_mem_nhdsWithin).and
    (((gt_mem_nhds (show (0:ℝ)<1 from by norm_num)).filter_mono
       (@nhdsWithin_le_nhds ℝ _ (0:ℝ) (Ioi (0:ℝ)))).and
      ((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hε)).eventually_ge_atTop K))).exists
  change c<1 at hc
  change K ≤ c^(-ε) at hbuy
  obtain ⟨s,hs,hρ⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (step c hc₀)
  refine ⟨K,hK,?_⟩
  filter_upwards [show ∀ᶠ r in trail, r∈Ioc (0:ℝ) s from
    mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨s,hs,subset_refl _⟩] with r hr t ht x
  let P (a:ℝ) := ‖(J a d).symm x‖
  let ζ : ℝ := -(d:ℝ)
  have hP (a:ℝ) : 0 ≤ P a := norm_nonneg _
  have hstep (a : ℝ) (ha : a∈Ioc 0 s) (u : ℝ) (hu : u∈Icc c 1) :
      P (u*a) ≤ K*u^ζ*P a := hρ ha u hu x
  have hpaid : K*c^ζ ≤ c^(ζ-ε) := by
    rw [sub_eq_add_neg,Real.rpow_add hc₀,mul_comm]
    exact mul_le_mul_of_nonneg_left hbuy (Real.rpow_nonneg hc₀.le _)
  have hincl (b:ℝ) (hb:b∈Ioc (0:ℝ) 1) : b*r∈Ioc 0 s :=
    ⟨mul_pos hb.1 hr.1, (mul_le_of_le_one_left hr.1.le hb.2).trans hr.2⟩
  have go (m:ℕ) (b:ℝ) (hb:b∈Ioc (0:ℝ) 1) (hm:c^m≤b) :
      P (b*r) ≤ K*b^(ζ-ε)*P r := by
    induction m generalizing b with
    | zero =>
      rw [pow_zero] at hm
      obtain rfl : b=(1:ℝ) := le_antisymm hb.2 hm
      simpa using le_mul_of_one_le_left (hP r) hK
    | succ m ih =>
      by_cases hp : c≤b
      · exact (hstep r hr b ⟨hp,hb.2⟩).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2 (by linarith only [hε])) (zero_le_one.trans hK)) (hP r))
      have hu : b/c∈Ioc (0:ℝ) 1 := ⟨div_pos hb.1 hc₀,(div_le_one hc₀).mpr (not_le.mp hp).le⟩
      specialize ih (b/c) hu (by rw [le_div_iff₀ hc₀]; exact hm)
      calc
        _ = P (c*((b/c)*r)) := by congr 1; field_simp
        _ ≤ K*c^ζ*P ((b/c)*r) := hstep _ (hincl _ hu) c ⟨le_rfl,hc.le⟩
        _ ≤ c^(ζ-ε)*(K*(b/c)^(ζ-ε)*P r) :=
          mul_le_mul hpaid ih (hP _) (Real.rpow_nonneg hc₀.le _)
        _ = _ := by
          have hx : c^(ζ-ε)*(b/c)^(ζ-ε)=b^(ζ-ε) := by
            rw [←Real.mul_rpow hc₀.le hu.1.le,mul_div_cancel₀ _ hc₀.ne']
          linear_combination K*P r*hx
  obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one ht.1 hc
  exact go m t ht hm.le

end YM.Integration.WilsonPhysicalExteriorFrame
