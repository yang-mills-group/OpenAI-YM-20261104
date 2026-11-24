import YM.Integration.FVA1Physical.Wilson.ClockComponents
import YM.FormalOPE.RG10.Second

/-! Actual analytic recalibrations preserve the nondegenerate Hessian of
the retained-history Laplace integral. Each primitive cost starts in
quadratic degree, so a nonconstant clock first enters in cubic degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Lattice RG YM.Wilson Tree RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial
open FVA2.CityHistory FVA2.RayScatter FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open FormalOPE.RG10.MultiGauge.Stack PowerSeries
open scoped Classical Topology ContDiff

private theorem clock_product_quad {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f g : E → ℝ}
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) (head : f 0 = 1) (sg : Stationary g) (y : E) :
    jet (f*g) 2 y = jet g 2 y := by
  have H := congrArg (fun A => coeff 2 (read y A)) (rise_mul (hf.of_le le_top) (hg.of_le le_top))
  simp only [read_rise,map_mul,Second.mul2,jet_zero,head,sg.base0,sg.base1,one_mul,mul_zero,add_zero] at H
  exact H

private theorem jet_total {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ℕ) (f : ℕ → E → ℝ) (hf : ∀ i ∈ s, ContDiffAt ℝ ω (f i) 0)
    (k : ℕ) (y : E) : jet (∑ i ∈ s, f i) k y = ∑ i ∈ s, jet (f i) k y := by
  induction s using Finset.induction_on with
  | empty => simp [jet]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,Inherit.plus _ (hf i (Finset.mem_insert_self ..))]
    · rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    rw [show ∑ j ∈ s, f j = fun x => ∑ j ∈ s, f j x from funext fun x => Finset.sum_apply ..]
    exact ContDiffAt.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))

variable {G : Gauge} {n c : Side} (d : Descent n c) (t : d.Tags) (u : Pins G c)
variable (h : d.OK G) (z : ℕ → ℝ → ℝ)
    (hot : ∀ i ≤ d.depth, ContDiffAt ℝ ω (z i) 0) (head : ∀ i ≤ d.depth, z i 0 = 1)

include h hot head in
theorem clockPhase_hessian (y : ℝ × Coordinates G d) :
    jet (clockPhase d t u z) 2 y = jet (rayPhase d t u) 2 y := by
  let s := Finset.range (d.depth+1)
  let P := atomAlong d t u
  let F i := (z i ∘ Prod.fst) * P i
  let A := FVA2.RayScatter.tax (E:=Coordinates G d) 1
  have hA : ContDiffAt ℝ ω A 0 := contDiffAt_const.mul (contDiffAt_fst.pow 2)
  have hP (i : ℕ) : ContDiffAt ℝ ω (P i) 0 := atom_hot d t u h i
  have scalar (i : ℕ) (hi : i ∈ s) : ContDiffAt ℝ ω (z i ∘ (Prod.fst : ℝ × Coordinates G d → ℝ)) 0 :=
    (hot i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).comp 0 contDiffAt_fst
  have hF (i : ℕ) (hi : i ∈ s) : ContDiffAt ℝ ω (F i) 0 := (scalar i hi).mul (hP i)
  have sums (L : ℕ → ℝ × Coordinates G d → ℝ) (hL : ∀ i∈s, ContDiffAt ℝ ω (L i) 0) :
      ContDiffAt ℝ ω (∑ i ∈ s, L i) 0 := by
    rw [show ∑ i ∈ s, L i = fun x => ∑ i ∈ s, L i x from funext fun x => Finset.sum_apply ..]
    exact ContDiffAt.sum hL
  have first : clockPhase d t u z = A + ∑ i ∈ s, F i := by
    funext x
    simp [clockPhase,A,F,P,s,FVA2.RayScatter.tax,Finset.sum_apply]
  have last : rayPhase d t u = A + ∑ i ∈ s, P i := by
    funext x
    rw [Pi.add_apply,Finset.sum_apply]
    change A x + consume d t 1 (recover u x) = A x + _
    change A x + d.account 1 t _ _ = A x + _
    rw [split_account]
    simp [s,P,atomAlong,consume]
  rw [first,last,Inherit.plus _ hA (sums F hF),Inherit.plus _ hA (sums P (fun i _ => hP i)),
    jet_total s F hF,jet_total s P (fun i _ => hP i)]
  congr 1
  exact Finset.sum_congr rfl fun i hi => clock_product_quad (scalar i hi) (hP i)
    (head i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (atom_stationary d t u h i) y

theorem clockPhase_coercive (room : d.Room G) {z : ℕ → ℝ → ℝ}
    (hot : ∀ i ≤ d.depth, ContDiffAt ℝ ω (z i) 0) (head : ∀ i ≤ d.depth, z i 0 = 1) :
    ∃ a > (0:ℝ), ∀ y, a * ‖y‖^2 ≤ jet (clockPhase d t u z) 2 y := by
  simpa only [clockPhase_hessian d t u (room_ok d room) z hot head] using rayPhase_coercive d t u room

end YM.Integration.FVA1Physical.Wilson
