import YM.Integration.WilsonCapturedPrimarySoftPartition

/-! The entire ordinary marked reading as an absolutely priced inventory
of actual soft words, on all original fields and on the same center hull. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySoftInventory
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Planned.GuardedAtom
open WilsonCapturedPrimarySoftPartition Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {o : V → Site n} {P : Rep G n} {Z : Support n}

theorem gather {J : Type} [Fintype J] (f : J → Config G n → ℂ) (fee : J→ℝ)
    (part : ∀j,WilsonCenteredSoftInventory.Receipt P Z (f j) (fee j)) :
    Nonempty (WilsonCenteredSoftInventory.Receipt P Z (fun U=>∑ j,f j U) (∑ j,fee j)) := by
  letI (j : J) : Countable (part j).Row := (part j).counted
  let I := (j : J) × (part j).Row
  let e (i : I) := (part i.1).price i.2
  let ground (i : I) := (part i.1).ground i.2
  let fields (i : I) := (part i.1).value i.2
  have entropy : SumBudget (fun i=>reservedMass P.p (ground i) (e i)) (∑ j,fee j) :=
    sigma_total _ fee (fun j=>(part j).cash) (budget_finite (fun j=>budget_nonneg (part j).cash) le_rfl)
  refine ⟨⟨I,inferInstance,ground,fields,e,fun i=>(part i.1).holds _,fun i=>(part i.1).gauge _,
    fun i=>(part i.1).borel _,fun i=>(part i.1).uses _,fun i=>(part i.1).nonnegative _,
    fun i=>(part i.1).cap _,entropy,?_⟩⟩
  intro U
  let c (i : I) := fields i U
  have ab : Summable (fun i : I=>‖c i‖) := (summable_sigma_of_nonneg (fun i=>norm_nonneg (c i))).mpr
    ⟨fun j=>((part j).posted U).summable.norm,Summable.of_finite⟩
  have pos := ab.of_norm
  have total : ∑' i,c i=∑ j,f j U := calc
    _ = ∑' j,∑' v,c ⟨j,v⟩ := pos.tsum_sigma
    _ = ∑ j,f j U := by
      rw [tsum_fintype]
      exact sum_congr rfl fun j _=>((part j).posted U).tsum_eq
  exact total ▸ pos.hasSum

def fare (p : BudgetPoint) (Z : Support n) (w : V→ℝ) (C : ℝ) (s : R.Mode) :=
  ∑q∈shards R s,tariff p Z w C q

theorem original [Countable ι] (L : Lamps X ι G P.p o R) (x : X) (s : R.Mode)
    (Z : Support n) (landing : ∀v∈s.val,o v∈Z)
    (w : V→ℝ) (hw : ∀v,0<w v) {C : ℝ} (paid : L.Paid w P.p.B (P.p.supportExponent+2) C) :
    Nonempty (WilsonCenteredSoftInventory.Receipt P Z (fun U=>(Poly.pass (L.log x U)).part s)
      (fare P.p Z w C s)) := by
  let qfun (q : ↥(shards R s)) (U : Config G n) := ∏ t∈q.val.val,(L.log x U).part t.val
  let cost (q : ↥(shards R s)) := tariff P.p Z w C q.val
  let each (q : ↥(shards R s)) := (WilsonCapturedPrimarySoftPartition.original L x s q.val q.property
    Z landing w hw paid).some
  have all := gather qfun cost each
  have same : (fun U=>∑q:↥(shards R s),qfun q U) = (fun U=>(Poly.pass (L.log x U)).part s) := by
    funext U
    have width : 0≤P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
    rw [pass_partition _ (L.quiet_of_hasSum x U (paid.sums width hw x U))]
    exact Finset.sum_coe_sort (shards R s) (fun q=>(∏t∈q.val,(L.log x U).part t.val))
  rw [same,show (∑ q : ↥(shards R s),cost q)=fare P.p Z w C s from Finset.sum_coe_sort (shards R s) (tariff P.p Z w C)] at all
  exact all

end YM.Integration.WilsonCapturedPrimarySoftInventory
