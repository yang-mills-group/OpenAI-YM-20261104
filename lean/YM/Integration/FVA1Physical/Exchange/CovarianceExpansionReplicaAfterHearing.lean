import YM.Integration.FVA1Physical.CommonCover.ReplicaRead

/-! Insert a previously paid original-law signed source comparison *after*
pairing with the exterior. Only the changed-vacuum term is bounded pointwise by
the two-draw covariation. The exterior may depend upon the whole trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Replica
open MeasureTheory Filter RG
open scoped Classical BigOperators
variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
variable {μ : Measure X} [SFinite μ] {ν : Measure T}

def submittedActionFee (μ : Measure X) (u v r : X → ℝ) (F : X → ℂ) :=
  (∫z,actionBill u v r z*‖F z.1-F z.2‖ ∂μ.prod μ) /
    (2*(∫x,u x ∂μ)*(∫x,v x ∂μ))

/-- A signed estimate on the uncut physical reading pays the first term.
The surviving integral tests the *filed* observable between the two vacua. -/
theorem signed_source_then_action
    (P : T → ℂ) (Y : T → ℂ) (F : T → X → ℂ) (env : ∀t,Envelope (F t))
    (k a b r : T → X → ℝ) (kn : ∀t x,0≤k t x) (ap : ∀t x,0<a t x)
    (bp : ∀t x,0<b t x) (rm : ∀t,Measurable (r t))
    (anchor:T→ℝ)(same:∀t x,Real.log (a t x)-Real.log (b t x)=r t x+anchor t) :
    let u:=fun t x=>k t x*a t x
    let v:=fun t x=>k t x*b t x
    let actualFiled:=fun t=>FrozenRead.meanOn μ (u t) (F t)
    let independent:=fun t=>FrozenRead.meanOn μ (v t) (F t)
    let toll:=fun t=>submittedActionFee μ (u t) (v t) (r t) (F t)
    (∀t,Integrable (u t) μ) → (∀t,Integrable (v t) μ) →
    (∀t,0<∫x,u t x ∂μ) → (∀t,0<∫x,v t x ∂μ) →
    Integrable (fun t=>Y t*(P t-actualFiled t)) ν →
    Integrable (fun t=>Y t*(actualFiled t-independent t)) ν →
    Integrable (fun t=>‖Y t‖*toll t) ν →
    ∀{B:ℝ}, ‖∫t,Y t*(P t-actualFiled t) ∂ν‖ ≤ B →
    ‖∫t,Y t*(P t-independent t) ∂ν‖ ≤ B+∫t,‖Y t‖*toll t ∂ν := by
  intro u v actualFiled independent toll ui vi up vp ia ib ic B source
  have diff(t):‖actualFiled t-independent t‖≤toll t:=by
    have raw:=reading (μ:=μ) (kn t) (ap t) (bp t) (rm t) (anchor t) (same t) (env t) (ui t) (vi t) (up t) (vp t)
    apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) (up t)) (vp t))).mpr
    exact (mul_comm ..).le.trans raw
  have vacuum:‖∫t,Y t*(actualFiled t-independent t) ∂ν‖ ≤ ∫t,‖Y t‖*toll t ∂ν:=by
    apply norm_integral_le_of_norm_le ic
    filter_upwards with t
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (diff t) (norm_nonneg _)
  have rows:(fun t=>Y t*(P t-independent t))= fun t=>Y t*(P t-actualFiled t)+Y t*(actualFiled t-independent t):=by
    funext t;ring
  rw [rows,integral_add ia ib]
  exact (norm_add_le ..).trans (add_le_add source vacuum)

/-- Ratio used by the original one-bond Haar posterior agrees exactly with the
common-fibre replica mean, including its own (possibly unnormalized) mass. -/
theorem haar_ratio (μ : Measure X) (u : X → ℝ) (F : X → ℂ) :
    (∫x,F x*(u x:ℂ) ∂μ)/(Complex.ofReal (∫x,u x ∂μ)) =
    FrozenRead.meanOn μ u F := by
  unfold FrozenRead.meanOn
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  have swap:(fun x=>F x*(u x:ℂ))=fun x=>(u x:ℂ)*F x:=by funext x;ring
  rw [swap,mul_comm]

/-- A field-independent partition factor cancels even on a zero-mass fibre. -/
theorem same_normalized_fibre (μ : Measure X) (u : X → ℝ) (F : X → ℂ) {c:ℝ} (hc:c≠0) :
    FrozenRead.meanOn μ (fun x=>c*u x) F=FrozenRead.meanOn μ u F := by
  unfold FrozenRead.meanOn
  have num:(∫x,(c*u x) • F x ∂μ) = c • ∫x,u x • F x ∂μ := by
    simp_rw [mul_smul]; rw [integral_smul]
  rw [integral_const_mul,num,smul_smul,mul_inv_rev,mul_assoc,inv_mul_cancel₀ hc,mul_one]

theorem haar_ratio_sub (μ : Measure X) (u:X→ℝ) (F H:X→ℂ)
    (fi:Integrable (fun x=>u x • F x) μ) (hi:Integrable (fun x=>u x • H x) μ) :
    FrozenRead.meanOn μ u F-FrozenRead.meanOn μ u H=
    (∫x,(F x-H x)*(u x:ℂ) ∂μ)/(Complex.ofReal (∫x,u x ∂μ)) := by
  rw [haar_ratio μ u (fun x=>F x-H x)]
  unfold FrozenRead.meanOn
  simp_rw [smul_sub]
  rw [integral_sub fi hi,smul_sub]

end YM.Integration.FVA1Physical.Replica
