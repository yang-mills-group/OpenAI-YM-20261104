import YM.Integration.WilsonOriginalPublicNodalSeed
import YM.Integration.WilsonOriginalPublicPivotSelf

/-! The reflected numerical coordinate is tested with the original two
Wilson insertions, their common filed K-source, and its signed earlier read. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 3500000
namespace YM.Integration.WilsonAddressedTrialSelfSensor
open Finset Function Lattice RG Wilson Source Labels MeasureTheory PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical RegulatorIR.FVAAlt2 Pert.Asymptotics
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkSeededPoint (seats)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalPublicPivotReflected (sampled evaluated board)
open WilsonOriginalPublicPivotCross (Film detector left right old)
open WilsonPositionProgramPublicWickGram (nodes reading)
open WilsonOriginalPublicNodalSeed (vector signed)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open scoped Classical BigOperators
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (d:Fin 2→ℕ){N per K f u:ℕ}(file:Filed R d K)(Y:∀i,R.family.label (d i))
    (fk:f≤K)(kn:K≤N)(ear:u≤K){L:Type}[Fintype L](o:L→Fin 2→ Lattice.Cover)(X:L→Sample 2)(μ:L→ℂ)
    (placed:∀l i,wrap (R.family.side K per) ((X l).layout i)=seats (R:=R) fk per (o l) i)
local notation "ν" => regulatorRun R.family N per K
local notation "chart" => vector R d (N:=N) (per:=per) file Y
local notation "raw_" => (fun l=>word R d f N per (fk.trans kn) (o l) Y)
local notation "K_" => (fun l=>product R d (N:=N) (seats (R:=R) fk per (o l))
  (doses R d file.station (N:=N) (per:=per) (file.A N per) Y))
local notation "phase" => (fun l=>WilsonOriginalTwoFlatGridScaling.gap R N per u (ear.trans kn) (raw_ l))
local notation "actual" => (∑l,μ l*R.family.omega N per (raw_ l))

private theorem compare {M:Type}[Fintype M](m x v z:M→ℂ)(g:M→ℝ)
    (h:∀i,‖x i-v i-z i‖≤g i):
    ‖(∑i,m i*v i)-∑i,m i*x i‖ ≤ (∑i,‖m i‖*g i)+‖∑i,m i*z i‖ := by
  have total : ‖∑i,m i*(x i-v i-z i)‖ ≤ ∑i,‖m i‖*g i := by
    apply (norm_sum_le univ (fun i=>m i*(x i-v i-z i))).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
  rw [norm_sub_rev]
  calc
    _ = ‖(∑i,m i*(x i-v i-z i)) + ∑i,m i*z i‖:=by
      simp only [mul_sub,Finset.sum_sub_distrib,sub_add_cancel]
    _ ≤ _:= (norm_add_le (∑i,m i*(x i-v i-z i)) (∑i,m i*z i)).trans (add_le_add total le_rfl)

include placed in
theorem weighted (q:ℕ)(due:L→ℝ)
    (spent:∀l,‖WilsonThermometerUnitFilingCoarse.reading R (N:=N)
         (RG16.Literal.credit R.family N per 0 (raw_ l) K kn) u ear-
       WilsonThermometerUnitFilingCoarse.reading R (N:=N) (numerator R N per K (K_ l)) u ear‖≤due l):
    ‖sampled R W d chart X μ univ q ν-actual‖ ≤
      (∑l,‖μ l‖*(‖phase l‖+due l))+‖∑l,μ l*signed R W d (N:=N) (per:=per) file Y ear (X l) q‖:=by
  apply compare μ (fun l=>R.family.omega N per (raw_ l))
    (fun l=>evaluated q ν (board R W d chart (X l) univ))
    (fun l=>signed R W d (N:=N) (per:=per) file Y ear (X l) q)
    (fun l=>‖phase l‖+due l)
  intro l
  exact (WilsonOriginalPublicNodalSeed.original R W d (N:=N) (per:=per)
    file Y fk kn ear (o l) (X l) (placed l) q (spent l)).2

include placed in
theorem original {B:Local.Physical.Deck G}{h:ℕ}{I:Type}[Fintype I]
    (axis:Axis)(leg:I→Glyph B h)(independent:Injective leg)(q:ℕ)(due:L→ℝ)
    (spent:∀l,‖WilsonThermometerUnitFilingCoarse.reading R (N:=N)
         (RG16.Literal.credit R.family N per 0 (raw_ l) K kn) u ear-
       WilsonThermometerUnitFilingCoarse.reading R (N:=N) (numerator R N per K (K_ l)) u ear‖≤due l)
    (one:(∑l,‖μ l‖*(‖phase l‖+due l))+‖∑l,μ l*signed R W d (N:=N) (per:=per) file Y ear (X l) q‖≤1):
    ∃k τ:ℝ,0<k ∧ 0<τ ∧ ∀(a:I→ℂ)(A B:I→Film W)(c z t e b:ℝ),
      let H:=detector W X μ q ν
      let U:=left R W d chart a A
      let V:=right R W d chart a B
      0≤c → 1≤z → 0≤t → e*t≤1 → e*t^2≤1 → b≤1 →
      ‖(fun i j=>H (A i*B j))-reading axis (nodes axis) leg‖≤τ →
      ‖actual‖≤c*z^2 → (∑i,‖H (A i*V)‖)≤e*t → (∑i,‖H (U*B i)‖)≤e*t →
      ‖old R W d chart X μ q ν+H (U*V)‖≤e*t^2+b → ‖a‖≤ max 1 ((c+5)/k)*z:=by
  obtain ⟨k,τ,kp,tp,hear⟩:=WilsonOriginalPublicPivotSelf.original R W axis leg independent
  refine ⟨k,τ,kp,tp,?_⟩
  intro a A B c z t e b H U V cp zp tp' small square last gram physical leftPaid rightPaid both
  exact hear d chart X μ q ν actual a A B c z t e b cp zp tp' small square last gram physical
    ((weighted R W d file Y fk kn ear o X μ placed q due spent).trans one) leftPaid rightPaid both

end YM.Integration.WilsonAddressedTrialSelfSensor
end
