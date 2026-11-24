import YM.Integration.WilsonMatrixTicketLanesVacuumKeptKernel
import YM.Integration.WilsonRegisteredPriorTables

/-! The earlier conditional covariance, third cumulant and all five parts
of the signed physical response for the same originally numbered hard activity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesVacuumKeptTable
open Function Set Filter MeasureTheory Lattice Wilson RG Marker
open IterationFour.Vacuum PhysicalNext.Repeat.Legato WilsonInvariantActionRegisteredHearing
open WilsonInvariantActionPriorHearing WilsonMatrixTicketLanesVacuumKept WilsonRegisteredPriorTables
open private factor_receipt from YM.Integration.OriginalMarkedRunAction
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m:ℕ} (j:m+1<N) (d:ℕ)
local notation "Ω" => Config G (R.family.side m per) × Config G (R.family.side (m+1) per)
local notation "P₁" => R.family.path.rep N per (m+1)
local notation "P₀" => R.family.path.rep N per m
local notation "Q" => OriginalMarkedRunAction.approximation R (p:=per) j d
local notation "E" => OriginalMarkedRunAction.remainder R (p:=per) j d
local notation "ν" => prior G (R.family.side (m+1) per)
local notation "μ" => prior G (R.family.side m per)
local notation "Z" => partition G (R.family.side N per) (R.family.path.β N per N)
local notation "cut" => OriginalMarkedRunAction.Comparison R (p:=per) j d

def indicated (i:ℕ) (U:Config G (R.family.side (m+1) per)):ℝ:=
  Real.exp (-(E).additive (R.alloy.B.a.budget (m+1)) U)*
    Real.exp ((Q).exponent U)*occurrence Q i U

theorem numerator (premium:cut) (i:ℕ) (V:Config G (R.family.side m per)) (U:Config G (R.family.side (m+1) per)):
    (hard R j i).val (V,U)=indicated R j d i U:=by
  let S:=ActualRunSpring.selected R N per (m+1) j
  have factor:=factor_receipt R j S d premium.posterior U
  have pos:0<(P₁).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson j.le U
  have nz:(Q).eval U≠0:=by
    intro zero
    rw [factor,zero,zero_mul] at pos
    exact (lt_irrefl _) pos
  calc
    _=(score R j (hard R j i)).val (V,U)*(P₁).eval U:=(div_mul_cancel₀ _ pos.ne').symm
    _=(_/((Q).eval U))*((Q).eval U*Real.exp (-(E).additive (R.alloy.B.a.budget (m+1)) U)):=by
      rw [hearing R j d i V U,factor,normalized,marked]
    _=indicated R j d i U*((Q).eval U*((Q).eval U)⁻¹):=by unfold indicated;ring
    _=_:=by rw [mul_inv_cancel₀ nz,mul_one]

def deposited (i:ℕ) (t:readings Ω) (V:Config G (R.family.side m per)):ℝ:=
  ∫U,(R.family.path.levels.clock.op m per).density (R.family.path.β N per (m+1)) U V*
    indicated R j d i U*t.val (V,U) ∂ν

theorem entry (premium:cut) (i:ℕ) (t:readings Ω) (V:Config G (R.family.side m per)):
    row R (N:=N) (t*score R j (hard R j i)) V=deposited R j d i t V:=by
  rw [mul_comm t _,raw R j]
  apply integral_congr_ae
  apply ae_of_all
  intro U
  dsimp only
  rw [numerator R j d premium i V U]
  rfl

private theorem vacuum (premium:cut) (i:ℕ) (V:Config G (R.family.side m per)):
    row R (N:=N) (score R j (hard R j i)) V=deposited R j d i 1 V:=by
  simpa only [one_mul] using entry R j d premium i 1 V

theorem earlier (premium:cut) (i:ℕ) (f h:readings Ω):
    let live:m<N:=by omega
    let I:=conditional R (p:=per) live
    let L:=WilsonInvariantActionPriorHearing.earlier R (p:=per) live
    let α:=L (I f)
    let β:=L (I h)
    let c:=L (I (f*h))-α*β
    let w:=score R j (hard R j i)
    covariance L (I w) (covariance I f h)+cubic L (I w) (I f) (I h)=
      Z⁻¹*∫V,(deposited R j d i 1 V/(P₀).eval V)*
        (row R (N:=N) (f*h) V-α*row R (N:=N) h V-β*row R (N:=N) f V+(α*β-c)*(P₀).eval V) ∂μ:=by
  intro live I L α β c w
  rw [WilsonRegisteredPriorTables.earlier_pair]
  simp only [w,vacuum R j d premium i]
  rfl

theorem response (premium:cut) (i:ℕ) (f h:readings Ω):
    let live:m<N:=by omega
    let J:=joint R (p:=per) live
    let α:=J f
    let β:=J h
    let c:=J (f*h)-α*β
    receipts R live f h (score R j (hard R j i)) =
      Z⁻¹*∫V,(deposited R j d i (f*h) V-α*deposited R j d i h V-
        β*deposited R j d i f V+(α*β-c)*deposited R j d i 1 V) ∂μ:=by
  intro live J α β c
  rw [WilsonRegisteredPriorTables.all_five]
  simp only [entry R j d premium i,vacuum R j d premium i]
  rfl

end YM.Integration.WilsonMatrixTicketLanesVacuumKeptTable
