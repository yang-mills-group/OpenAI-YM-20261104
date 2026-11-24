import YM.Integration.FVA1Physical.Sources.Round2.FieldUtopia

/-! Uniform stage salary for every fixed mixed physical source in the growing
local collar. The zero support exponent actually used by the Gaussian ratio costs
a single constant despite the increasing number and changing positions of sites. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Cacao MSbar.Rolling MSbar.Midpoint Push.Uniform Next.SectorChange
open MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Lapaz
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

theorem collar_weight (L : ℕ) {y : ℝ} (h : 1 ≤ hatW y) :
    liftW (αm y) 0 (L*closeN y) ≤ Real.exp (8*(L:ℝ)) := by
  simp only [liftW,pow_zero,one_mul]
  apply Real.exp_monotone
  have hy : 0<hatW y:=zero_lt_one.trans_le h
  have hr : (radiusB y:ℝ) ≤ 2*hatW y:=by
    have upper : (radiusB y:ℝ)<hatW y+1:=Nat.ceil_lt_add_one hy.le
    linarith only [upper,h]
  have hz : ((L*closeN y:ℕ):ℝ) ≤ (L:ℝ)*(2*hatW y)^3:=by
    unfold closeN;push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hr 3) (Nat.cast_nonneg _)
  have hα : 0 ≤ αm y:=zpow_nonneg hy.le _
  refine (mul_le_mul_of_nonneg_left hz hα).trans_eq ?_
  unfold αm;rw [_root_.zpow_neg];change ((hatW y)^3)⁻¹ * _ = _
  field_simp; ring

theorem field_vault_fixed (p m L : ℕ) (part : Bool) :
    ∃ C:ℝ, 0 ≤ C ∧ ∀ y:ℝ, 1 ≤ hatW y → ∀ (A : Mosaic.Issue G) (o : ι→Site A.f) (b : Site A.f),
      (∀ j:Slice J, separation b (legs J o j).1 ≤ L*closeN y) → ∀ i ≤ p,
      Vault (address A.F G) {b} (αm y) 0 m 0 (PowerSeries.coeff i (jointFieldBank J A o part)) C ∧
      (PowerSeries.coeff i (jointFieldBank J A o part)).totalDegree ≤ i := by
  choose B e hB native using fun (u:Finset (Slice J)) (i:Fin (p+1))=>
    fixed_polynomial_vault (lampRow J part u i.val) m
  let w:=Real.exp (8*(L:ℝ))
  have hw : 1 ≤ w:=Real.one_le_exp (by positivity)
  let price (r:Finset (Slice J)×Fin (p+1)):=B r.1 r.2*w^e r.1 r.2
  have nonneg r : 0 ≤ price r:=mul_nonneg (hB ..) (pow_nonneg (zero_le_one.trans hw) _)
  refine ⟨∑ r,price r,sum_nonneg (fun r _=>nonneg r),?_⟩
  intro y hy A o b close i hi
  let u:=activeSlots J A.S A.F o
  let ni:Fin (p+1):=⟨i,by omega⟩
  have α0 : 0 ≤ αm y := zpow_nonneg (zero_le_one.trans hy) _
  have loc (j:Wire G (↑u)) : liftW (αm y) 0 (separation b (address A.F G (jointSlot J A.S A.F o j))) ≤ w:=
    (w_more (close j.1.val) α0 0).trans (collar_weight L hy)
  have paid:=native u ni (address A.F G) b (jointSlot J A.S A.F o) 0 (αm y) w α0 hw loc
  rw [jointFieldBank,PowerSeries.coeff_mk]
  exact ⟨Quote.widen paid (single_le_sum (fun r _=>nonneg r) (mem_univ (u,ni))) le_rfl,
    (MvPolynomial.totalDegree_rename_le ..).trans (lampRow_degree J part u i)⟩

/-- Direct conversion of a constant source budget into the actual stage salary
purchased by `Mosaic.Issue.portion`. It is uniform in the input/output period. -/
theorem field_projection_budget (p k L : ℕ) (part : Bool) (hk : 1 ≤ k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y:ℝ, 1 ≤ hatW y → ∀ (A:Mosaic.Issue G) (o:ι→Site A.f) (b : Site A.f),
      (∀ j:Slice J,separation b (legs J o j).1 ≤ L*closeN y) →
      let σ:=k*(p+2);let rad:=A.S.patch.L.val*closeN y
      ∀ i ≤ p,Vault (address A.F G) {b} (αm y) 0 σ 0 (PowerSeries.coeff i (jointFieldBank J A o part))
        ((plateD b (αm y) p 0 σ k rad C)^k) ∧
        (PowerSeries.coeff i (jointFieldBank J A o part)).totalDegree ≤ σ := by
  obtain ⟨C,hC,bank⟩:=field_vault_fixed J p (k*(p+2)) L part
  let B:=max C 1
  have hB : 1 ≤ B:=le_max_right ..
  refine ⟨B,hB,?_⟩
  intro y hy A o b near σ rad i hi
  obtain ⟨v,deg⟩:=bank y hy A o b near i hi
  have a0 : 0 ≤ αm y:=zpow_nonneg (zero_le_one.trans hy) _
  have w1 : 1 ≤ liftW (αm y) 0 rad:=w_start a0 0 _
  have paid : B ≤ plateD b (αm y) p 0 σ k rad B := by
    unfold plateD
    have hb0:=zero_le_one.trans hB
    calc B ≤ liftW (αm y) 0 rad*B := le_mul_of_one_le_left hb0 w1
      _ ≤ 2^σ*(liftW (αm y) 0 rad*B) := le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans w1) hb0) (one_le_pow₀ (by norm_num))
      _ ≤ ((p+1:ℕ):ℝ)*(2^σ*(liftW (αm y) 0 rad*B)) := le_mul_of_one_le_left (by positivity) (by exact_mod_cast Nat.succ_pos p)
      _ ≤ 2^k*(((p+1:ℕ):ℝ)*(2^σ*(liftW (αm y) 0 rad*B))) :=le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      _ ≤ 1+_ := le_add_of_nonneg_left zero_le_one
  have pp:=hB.trans paid
  refine ⟨Quote.widen v ((le_max_left ..).trans (paid.trans ((le_of_eq (pow_one _).symm).trans (pow_le_pow_right₀ pp hk)))) le_rfl,?_⟩
  exact deg.trans (hi.trans ((Nat.le_add_right p 2).trans ((by simpa only [σ,one_mul] using Nat.mul_le_mul_right (p+2) hk) : p+2 ≤ σ)))

end YM.Integration.FVA1Physical.Round2.Curvature
