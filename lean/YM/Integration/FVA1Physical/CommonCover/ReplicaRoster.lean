import YM.Integration.FVA1Physical.CommonCover.ReplicaRead

/-! A complete weighted family of conditional mixed readings uses one pair
of fine configurations and one capped action increment, including on failed
fields. The same source family occurs on both sides. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Replica
open MeasureTheory Filter RG Finset
open scoped Classical BigOperators
variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def diameter (s : Finset ι) (w : ι → ℝ) (F : ι → X → ℂ) (z : X × X) : ℝ :=
  ∑ i ∈ s, w i*‖F i z.1-F i z.2‖

theorem reading_roster (s : Finset ι) (w : ι → ℝ) (wn : ∀i,0≤w i) (F : ι → X → ℂ)
    (env : ∀i,Envelope (F i)) {k a b r : X → ℝ} (kn : ∀x,0≤k x) (ap : ∀x,0<a x) (bp : ∀x,0<b x)
    (rm : Measurable r) (anchor : ℝ) (same : ∀x,Real.log (a x)-Real.log (b x)=r x+anchor) :
    let u := fun x => k x*a x
    let v := fun x => k x*b x
    Integrable u μ → Integrable v μ → 0<(∫x,u x ∂μ) → 0<(∫x,v x ∂μ) →
      2*(∫x,u x ∂μ)*(∫x,v x ∂μ)*(∑i ∈ s,w i*‖FrozenRead.meanOn μ u (F i)-FrozenRead.meanOn μ v (F i)‖) ≤
        ∫z,actionBill u v r z*diameter s w F z ∂μ.prod μ := by
  intro u v ui vi up vp
  have ib := integrable_bill ui vi (fun x => mul_nonneg (kn x) (ap x).le) (fun x=>mul_nonneg (kn x) (bp x).le) rm
  let B := actionBill u v r
  let Z := 2*(∫x,u x ∂μ)*(∫x,v x ∂μ)
  let d := fun i => ‖FrozenRead.meanOn μ u (F i)-FrozenRead.meanOn μ v (F i)‖
  let slice := fun i (z:X×X) => B z*‖F i z.1-F i z.2‖
  have one (i) : Z*d i ≤ ∫z,slice i z ∂μ.prod μ :=
    reading kn ap bp rm anchor same (env i) ui vi up vp
  have joint (z) : B z*diameter s w F z=∑i ∈ s,w i*slice i z := by
    rw [diameter,Finset.mul_sum]; apply sum_congr rfl; intro i _; dsimp only [slice]; ring
  change Z*(∑i ∈ s,w i*d i) ≤ ∫z,B z*diameter s w F z ∂μ.prod μ
  simp_rw [joint]; rw [integral_finsetSum _ (fun i _ => (cost_times_diameter ib (env i)).const_mul (w i)),Finset.mul_sum]
  apply sum_le_sum; intro i _
  rw [integral_const_mul,mul_left_comm Z]
  exact mul_le_mul_of_nonneg_left (one i) (wn i)

end YM.Integration.FVA1Physical.Replica
