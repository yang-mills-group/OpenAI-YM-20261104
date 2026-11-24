import YM.Integration.FVA1Physical.TwoReset.CopyLetters

/-! Read the formal packet on every testing period that is a
multiple of its support period, in powers of its coupling. These probes
continue into the next step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V ι α : Type} [DecidableEq V] [Fintype V] {c f n : Side}
  {J : Passport n V} {R : Census V}
variable (h : n.val ∣ f.val) (M : ι→Row J R G α) (w : V→ℕ)
    (L : Layout G) (T : Finset Age)
variable (t : α) (x : Stationary.Link G f) (i : ℕ)
set_option quotPrecheck false

local notation "paint" => (fun j:ι=> (M j).paint t)
local notation "ι'" => Fin (Pages n f)
local notation "s" => Stationary.arm G f 1 x
local notation "M₁" u:max => (fun j:ι=> TwoReset.copy h (M j) u)
local notation "E" u:max => Air.craft (M₁ u) paint w L T
local notation "Z" => copyColor h M w paint L T

abbrev peek (d:ℕ) (y:Stationary.Link G f) := Air.discharge (copyColor h M w (fun j:ι=>(M j).paint t) L T)
  d (Stationary.arm G f 1 y)

def reading (j:ι) (u : Fin (Pages n f)) : Poly R :=
  Poly.send (M j).mode ((M j).paint t * Complex.ofReal ((TwoReset.copy h (M j) u).markReceipt i x))

variable {a : ℝ} {k : ℕ} (H : Air.Staff M (fun j:ι=> (M j).paint t) w a k)

local notation "views" u:max => Air.discharge (E u) i s
include H
omit [Fintype V] in
lemma peek_pages : peek h M w L T t i x = ∑ u:Fin (Pages n f),views u := by
  apply Marker.Poly.ext
  intro j
  let W u : Colors R G f := E u
  rw [Poly.part_sum]
  by_cases hh : j=R.quiet
  · subst j
    unfold peek Air.discharge
    simp only [Multi.part_lit_quiet,Finset.sum_const_zero]
  let v : Multi.Hot R:= ⟨j,(Cumulants.hot_iff_ne j).2 hh⟩
  change (Air.discharge Z i s).part v.val = ∑ u:Fin (Pages n f), (Air.discharge (W u) i s).part v.val
  unfold Air.discharge
  simp_rw [part_lit _ v]
  let g (u:ι') := projected ((W u).mark v)
  rw [show projected ((Z).mark v) = ∑ u:ι', g u from funext (fun i=> by
    unfold projected copyColor
    simp only [Finset.sum_apply]; rfl)]
  nth_rw 1 [Assembly.jet]
  rw [iteratedFDeriv_sum_apply (fun u _=>
      ((Air.grade (M₁ u) paint w (copy_staff h M w paint H u) L T v).smooth).of_le le_top),
    _root_.sum_apply,Finset.smul_sum]; rfl

lemma total_peek : HasSum (fun j=> ∑ u: Fin (Pages n f), reading h M t x i j u)
    (peek h M w L T t i x) := by
  rw [peek_pages h M w L T t x i H]
  let F u := Air.craft (M₁ u) paint w L T
  have Hp (u:ι') : HasSum (fun j=> reading h M t x i j u) (views u):=
    Air.compared (M₁ u) paint w (copy_staff h M w paint H u) L T x i
  exact hasSum_sum (f:=fun u j=> reading h M t x i j u) (fun u _ => Hp u)

lemma reads_page (u : ι') : HasSum (fun j=> reading h M t x i j u) (views u):=
    Air.compared (M₁ u) paint w (copy_staff h M w paint H u) L T x i
end YM.Integration.FVA1Physical.TwoReset
