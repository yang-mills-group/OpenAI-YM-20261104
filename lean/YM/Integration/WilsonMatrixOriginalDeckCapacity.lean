import YM.PhysMS.Frame.Cost

/-! Sharp relative length estimates on the original leading frame. The
    physical and inverse norms are priced on the same two actual scales;
    the threshold precedes all vectors and relative lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckCapacity
open Function Filter Set Finset Spec Climb OPE PhysMS Trace.Pilot Extra.FD RG12.Roof
open scoped Topology Classical BigOperators
theorem simultaneous {X:Type*} (K ζ ε : ℝ) (hK : 1 ≤ K) (he : 0 < ε)
    (price:ℝ→X→ℝ) (nonnegative:∀r x,0≤price r x)
    (h : ∀ c : ℝ, 0 < c → c < 1 → ∀ᶠ r in trail, ∀ a∈Set.Icc c 1,
          ∀x,price (a*r) x ≤ K*a^ζ*price r x) :
    ∀ᶠ r in trail, ∀ a : ℝ, a∈Set.Ioc 0 1 → ∀x,price (a*r) x ≤ K*a^(ζ-ε)*price r x := by
  -- Choose a step small enough to already absorb K in the exponent.
  obtain ⟨c,hc0,hc,hε⟩ := ((show ∀ᶠ c : ℝ in trail, 0 < c from self_mem_nhdsWithin).and
    (((gt_mem_nhds (show (0:ℝ)<1 from by norm_num)).filter_mono (@nhdsWithin_le_nhds ℝ _ (0:ℝ) (Set.Ioi (0:ℝ)))) |>.and
    ((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr he)).eventually_ge_atTop K))).exists
  change c<1 at hc
  change K ≤ c^(-ε) at hε
  obtain ⟨s,hs,hρ⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp (h c hc0 hc)
  have hsmall : ∀ᶠ r in trail, r∈ Set.Ioc 0 s:= mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨s,hs,subset_refl _⟩
  filter_upwards [hsmall] with r hr a ha x
  let P:=fun t=>price t x
  have hP:∀t,0≤P t:=fun t=>nonnegative t x
  have hR : 0 < r:= hr.1
  have haken : K*c^ζ ≤ c^(ζ-ε):=by
     rw [sub_eq_add_neg,Real.rpow_add hc0,mul_comm]; exact mul_le_mul_of_nonneg_left hε (Real.rpow_nonneg hc0.le _)
  have hincl (b : ℝ) (hb : b∈Set.Ioc (0:ℝ) 1) : b*r∈Set.Ioc 0 s:=
    ⟨mul_pos hb.1 hr.1,le_trans (mul_le_of_le_one_left hr.1.le hb.2) hr.2⟩
  -- for every a >= c^m. recurse until scale back to r, use same m cost if needed
  have go(m : ℕ) (b : ℝ) (hb : b∈Set.Ioc 0 1) (hstep : c^m ≤ b) :
      P (b*r) ≤ K*b^(ζ-ε)*P r := by
    induction m generalizing b with
    | zero =>
      rw [pow_zero] at hstep; obtain rfl : b = (1:ℝ) := le_antisymm hb.2 hstep
      simpa using (le_mul_of_one_le_left (hP r) hK)
    | succ m ih =>
      have h0 : 0 < b:= hb.1
      by_cases hp : c ≤ b
      · calc _ ≤ K*b^ζ*P r:= hρ hr b ⟨hp,hb.2⟩ x
             _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                      (Real.rpow_le_rpow_of_exponent_ge h0 hb.2 (by linarith only [he])) (zero_le_one.trans hK)) (hP r)
      have hu : b / c∈ Set.Ioc 0 1 := ⟨div_pos h0 hc0,(div_le_one hc0).mpr (not_le.mp hp).le⟩
      specialize ih (b / c) hu (by rw [le_div_iff₀ hc0]; exact hstep)
      calc
        _ = P (c*((b/c)*r)) := by congr 1; field_simp
        _ ≤ K*c^ζ * P (b/c * r) := hρ (hincl (b/c) hu) c ⟨le_rfl,hc.le⟩ x
        _ ≤ c^(ζ-ε) * (K*(b/c)^(ζ-ε)*P r) := mul_le_mul haken ih (hP _) (Real.rpow_nonneg hc0.le _)
        _ = _:=by
          have hx : c^(ζ-ε) * (b/c)^(ζ-ε) = b^(ζ-ε):=by rw [← Real.mul_rpow hc0.le hu.1.le, mul_div_cancel₀ _ hc0.ne']
          linear_combination K*P r*hx
  obtain ⟨m,hm⟩:= exists_pow_lt_of_lt_one ha.1 hc
  exact go m a ha hm.le

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(d:ℕ)(J:ℝ→tower S)
def capacity (r:ℝ)(z:S.Field d):ℝ:=‖(J r d).symm z‖

theorem gear :∃M:ℝ,0≤M ∧ ∀a:ℝ,0≤a→∀z,‖Pert.Scale.gear C.labels d a z‖≤M*(max 1 a)^d*‖z‖:=by
 let B:=recorded C.labels d
 let M:=∑i,‖B.b i‖*‖(B.b.coord i).toContinuousLinearMap‖
 refine ⟨M,sum_nonneg (fun i _=>mul_nonneg (norm_nonneg _) (B.b.coord i).toContinuousLinearMap.opNorm_nonneg),?_⟩
 intro a ap z
 nth_rw 1 [←B.b.sum_repr z]
 rw [map_sum]
 simp only [M,sum_mul]
 apply (norm_sum_le ..).trans;apply sum_le_sum;intro i _
 rw [map_smul,Pert.Scale.rare,norm_smul,norm_smul,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg ap]
 have exp:a^(B.w i).1≤(max 1 a)^d:=(pow_le_pow_left₀ ap (le_max_right 1 a) _).trans (pow_le_pow_right₀ (le_max_left 1 a) (B.cap i))
 calc
  _≤(‖(B.b.coord i).toContinuousLinearMap‖*‖z‖)*((max 1 a)^d*‖B.b i‖):=mul_le_mul ((B.b.coord i).toContinuousLinearMap.le_opNorm z) (mul_le_mul_of_nonneg_right exp (norm_nonneg _)) (mul_nonneg (pow_nonneg ap _) (norm_nonneg _)) (by positivity)
  _=_:=by ring

theorem local_step (lead:Leading F J):∃K:ℝ,1≤K ∧ ∀c:ℝ,0<c→c<1→∀ᶠr in trail,∀a∈Set.Icc c 1,∀z:S.Field d,
 capacity d J (a*r) z≤K*a^(-(d:ℝ))*capacity d J r z ∧ capacity d J r z≤K*capacity d J (a*r) z:=by
 obtain ⟨M,m0,cost⟩:=gear (C:=C) d
 obtain ⟨B,b1,measured⟩:=Frame.comparison F d J lead
 let K:=max 1 (B*M);refine ⟨K,le_max_left ..,fun c cp _=>?_⟩
 filter_upwards [measured c cp] with r hr a ha z
 have ap:=cp.trans_le ha.1
 let A:=(J r d).symm z;let Z:=(J (a*r) d).symm z
 let b:=Frame.cocycle d J r a ap
 have eq:A=Pert.Scale.gear C.labels d a (b Z):=by
  apply (J r d).injective;rw [Frame.cocycle_value];exact (LinearEquiv.apply_symm_apply ..).trans (LinearEquiv.apply_symm_apply ..).symm
 have inverse:b Z=Pert.Scale.gear C.labels d a⁻¹ A:=by rw [eq,Pert.Scale.gear_inverse C.labels ap.ne']
 have back:Z=b.symm (Pert.Scale.gear C.labels d a⁻¹ A):=by rw [←inverse,b.symm_apply_apply]
 have b0:=zero_le_one.trans b1
 have ge:1≤a⁻¹:=(one_le_inv₀ ap).mpr ha.2
 have s:=cost a ap.le (b Z)
 have l:=cost a⁻¹ (inv_pos.mpr ap).le A
 rw [max_eq_left ha.2,one_pow,mul_one] at s;rw [max_eq_right ge] at l
 have cB:=hr a ha
 change ‖Z‖≤K*a^(-(d:ℝ))*‖A‖ ∧ ‖A‖≤K*‖Z‖
 constructor
 · rw [Real.rpow_neg ap.le,Real.rpow_natCast,←inv_pow]
   calc
    ‖Z‖ =‖b.symm (Pert.Scale.gear C.labels d a⁻¹ A)‖:=congrArg norm back
    _≤B*(M*(a⁻¹)^d*‖A‖):=(cB.2 _).trans (mul_le_mul_of_nonneg_left l b0)
    _=(B*M)*((a⁻¹)^d*‖A‖):=by ring
    _≤K*((a⁻¹)^d*‖A‖):=mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
    _=_:=by ring
 · calc
    ‖A‖ =‖Pert.Scale.gear C.labels d a (b Z)‖:=congrArg norm eq
    _≤M*(B*‖Z‖):=s.trans (mul_le_mul_of_nonneg_left (cB.1 _) m0)
    _=(B*M)*‖Z‖:=by ring
    _≤K*‖Z‖:=mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)

private theorem reverse {v w k:ℝ}(vp:0<v)(wp:0<w)(h:v≤k*w):w⁻¹≤k*v⁻¹:=by
 rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ wp vp];simpa using h

theorem original (lead:Leading F J):∃K:ℝ,1≤K ∧ ∀ε:ℝ,0<ε→∀ᶠr in trail,∀a∈Set.Ioc (0:ℝ) 1,∀z:S.Field d,
 capacity d J (a*r) z≤K*a^(-(d:ℝ)-ε)*capacity d J r z ∧ capacity d J r z≤K*a^(-ε)*capacity d J (a*r) z:=by
 obtain ⟨K,k1,steps⟩:=local_step F d J lead
 have nn (r:ℝ)(z:S.Field d):0≤capacity d J r z:=norm_nonneg _
 have pos (r:ℝ){z:S.Field d}(nz:z≠0):0<capacity d J r z:=norm_pos_iff.mpr fun eq=>nz ((J r d).symm.map_eq_zero_iff.mp eq)
 refine ⟨K,k1,fun ε ep=>?_⟩
 have forward:=simultaneous K (-(d:ℝ)) ε k1 ep (capacity d J) nn (fun c cp co=>(steps c cp co).mono fun r hr a ha z=>(hr a ha z).1)
 have backwards:=simultaneous K 0 ε k1 ep (fun r z=>(capacity d J r z)⁻¹) (fun r z=>inv_nonneg.mpr (nn r z)) (fun c cp co=>(steps c cp co).mono fun r hr a ha z=>by
   rw [Real.rpow_zero,mul_one]
   by_cases nz:z=0
   · simp [nz,capacity]
   · exact reverse (pos r nz) (pos (a*r) nz) (hr a ha z).2)
 filter_upwards [forward,backwards] with r hf hb a ha z
 refine ⟨hf a ha z,?_⟩;by_cases nz:z=0
 · simp [nz,capacity]
 · simpa only [zero_sub,inv_inv] using reverse (inv_pos.mpr (pos (a*r) nz)) (inv_pos.mpr (pos r nz)) (hb a ha z)

end YM.Integration.WilsonMatrixOriginalDeckCapacity
