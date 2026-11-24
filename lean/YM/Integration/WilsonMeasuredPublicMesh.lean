import YM.Integration.WilsonMeasuredPublicPacket
import YM.Integration.WilsonExternalMeshMass

/-! The original joint smooth profile costs its continuum L¹ mass on the physical separated packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicMesh
open Function Filter Set MeasureTheory Finset Table Lattice Wilson RG Cells Extraction Spec Climb OPE
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicSlots WilsonMeasuredPublicCopies WilsonMeasuredPublicLayout WilsonExternalMeshMass
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {l : Ultrafilter (ℕ×ℕ)} {n:ℕ}
    {d : Fin n → ℕ} {v : ∀i,S.Field (d i)} {s B:Fin n → ℝ}
    (L:∀i,Slot F l (d i) (v i) (s i) (B i))
local notation "wage" => amount (F:=F) (B:=B) (s:=s) (v:=v)
def tokens (q:ℕ×ℕ) (i:Fin n) : R.family.book.Token := ⟨d i,(L i).arm.source q⟩

/-- Placement is required only where the true joint test is nonzero. -/
def Admits (t : Test n) (q:ℕ×ℕ) : Prop :=
  ∀ u : Var R.family.S n q.1 q.2,t (Order.cells R.family q.1 q.2 u)≠0 →
    Nonempty (Placed R.family (fun i=>(L i).m) u)

theorem finite (t:Test n) {η:ℝ} (positive:0<η) :
    ∀ᶠ q:ℕ×ℕ in f.fuse,Admits L t q →
      ‖Order.smears R.family q.1 q.2 (tokens L q) t‖ ≤ ((∫x:Points n,‖t x‖)+η)*(∏i,wage i) := by
  filter_upwards [eventually_all.mpr fun i=>(L i).reflected,WilsonExternalMeshMass.regulated R.family f t positive]
    with q bought mass
  intro placed
  have nonnegative : 0≤∏i,wage i := prod_nonneg fun i _=>(bought i).cost
  have heard (y:Var R.family.S n q.1 q.2) (live:t (Order.cells R.family q.1 q.2 y)≠0) :
      ‖R.family.numeric q.1 q.2 (tokens L q) y‖ ≤ ∏i,wage i :=
    (WilsonMeasuredPublicPacket.heard L q bought y (placed y live).some).1
  have pay (y:Var R.family.S n q.1 q.2) :
      ‖charge R.family t y * R.family.numeric q.1 q.2 (tokens L q) y‖ ≤ ‖charge R.family t y‖*(∏i,wage i) := by
    by_cases live:t (Order.cells R.family q.1 q.2 y)=0
    · simp [charge,live]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (heard y live) (norm_nonneg _)
  have exactSum : Order.smears R.family q.1 q.2 (tokens L q) t=
      ∑ y:Var R.family.S n q.1 q.2, charge R.family t y * R.family.numeric q.1 q.2 (tokens L q) y := by
    simp only [Order.smears,mul_sum,charge]
    exact sum_congr rfl fun _ _=>(mul_assoc ..).symm
  rw [exactSum]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum fun y _=>pay y).trans
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right mass nonnegative

theorem continuum (order : (l:Filter (ℕ×ℕ))≤f.fuse) (t:Test n)
    (placed : ∀ᶠ q:ℕ×ℕ in f.fuse,Admits L t q) :
    ‖t.applyTo (fun x=>S.classMoment S d x v)‖ ≤ (∫x:Points n,‖t x‖)*(∏i,wage i) := by
  have read := (WilsonMeasuredPublicCopies.smooth order L t).norm
  have bound (η:ℝ) (positive:0<η) := le_of_tendsto read
    ((placed.mp (finite L t positive)).filter_mono order)
  have descent : Tendsto (fun η:ℝ=>((∫x:Points n,‖t x‖)+η)*(∏i,wage i))
      (𝓝[>] (0:ℝ)) (𝓝 ((∫x:Points n,‖t x‖)*(∏i,wage i))) := by
    have step : Tendsto (fun η:ℝ=>(∫x:Points n,‖t x‖)+η) (𝓝[>] (0:ℝ)) (𝓝 ((∫x:Points n,‖t x‖)+0)) :=
      tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds)
    simpa only [add_zero] using step.mul_const (∏i,wage i)
  exact ge_of_tendsto descent ((show ∀ᶠ η:ℝ in 𝓝[>] 0,0<η from self_mem_nhdsWithin).mono fun η h=>bound η h)

end YM.Integration.WilsonMeasuredPublicMesh
