import YM.Integration.WilsonReportingMeasuredWardFixedStock

/-! Finite-order inversion of the actual prescribed curvature columns, retaining their scalar parts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardInverse
open Function Finset Lattice Wilson RG Source Labels MS.Local.Physical MS.Theater MS.Land
open Trace.Physical Trace.Physical.GermGraph Next.Rank.Price WilsonMatrixTicketLanesNativePrices
open PhysicalNext.Repeat.Legato WilsonReportingPrescribedOldFreeArms
open WilsonReportingPrescribedOldWardWallet WilsonReportingPrescribedOldWardTree
open WilsonReportingMeasuredWardFees WilsonReportingMeasuredWardSource
open scoped Classical BigOperators

variable {G:Gauge} {B:Deck G} (Q:Prescription B)
local notation "I" => B.BIndex (4:ℤ) 2

/-- Each coefficient depends only on the requested coefficients up to that same order. -/
def submit (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ) : I→ℂ := fun j=>
  v k j-∑i:Fin k,(projected Q clock (k-i.val) (0,submit clock v i.val)).2 j
termination_by k
decreasing_by exact i.isLt

theorem columns (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ) (j:I):
    (∑i:Fin (k+1),(projected Q clock (k-i.val) (0,submit Q clock v i.val)).2 j)=v k j := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.sub_self,WilsonReportingMeasuredWardFixedStock.matrix_zero]
  have last:submit Q clock v k j=v k j-∑i:Fin k,(projected Q clock (k-i.val) (0,submit Q clock v i.val)).2 j:=submit.eq_1 ..
  rw [last]
  abel

variable (R:Run G)

def intercept (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ):ℂ :=
  ∑i:Fin (k+1),scalar R Q (0,submit Q clock v i.val) clock (k-i.val)

def previous (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ) (n:Side) (o:Site n) (U:Config G n):ℂ:=
  ∑i:Fin (k+1),operand R Q (0,submit Q clock v i.val) clock (k-i.val) n o U

theorem proceeds (simple:G.Simple) (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ) (n:Side) (o:Site n) (U:Config G n):
    previous Q R clock v k n o U=intercept Q R clock v k+stencil R (0,v k) n o U := by
  unfold previous
  simp only [split R Q simple,Finset.sum_add_distrib,intercept]
  congr 1
  unfold stencil
  rw [Finset.sum_comm]
  exact sum_congr rfl (fun i _=>by rw [←sum_mul,columns])

theorem rolled (w:ℂ) (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ):
    (∑i:Fin (k+1),
      let z:Stock B:=(0,submit Q clock v i.val)
      scalar R Q z clock (k-i.val) • (R.family.labels.level 4).e0+
        w • coordinates R (projected Q clock (k-i.val) z))=
      intercept Q R clock v k • (R.family.labels.level 4).e0+w • coordinates R (0,v k):=by
  dsimp only
  rw [Finset.sum_add_distrib,←Finset.sum_smul,←Finset.smul_sum]
  congr 2
  unfold coordinates
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  let h:R.family.label 4:=(warehouse R).fits B 4 2 j
  let f (i:Fin (k+1)):=(projected Q clock (k-i.val) (0,submit Q clock v i.val)).2 j
  change (∑i:Fin (k+1),f i • h)=v k j • h
  calc
    _=(∑i:Fin (k+1),f i) • h:=Finset.sum_smul.symm
    _=_:=congrArg (fun c:ℂ=>c • h) (columns Q clock v k j)

variable {R} {T:Campaign R} (W:Campaign.Pillars R T) {m N per:ℕ}
local notation "F" => R.family.labels.level 4
local notation "S" => R.family.localSection 4
local notation "P" => R.family.path.rep N per m

theorem measured (simple:G.Simple) (age:R.family.ref 4 ≤ m) (life:m ≤ N) (clock:ℝ)
    (v:ℕ→I→ℂ) (k:ℕ) (o:Site (R.family.side m per)) (U:Config G (R.family.side m per)):
    (∑i:Fin (k+1),(WilsonReportingMeasuredWardIntake.charged W Q life o (0,submit Q clock v i.val) clock (k-i.val)).density o S P U)=
      (R.family.S.a m:ℂ)^4*((P).eval U:ℂ)*(intercept Q R clock v k+stencil R (0,v k) _ o U) := by
  rw [←proceeds Q R simple clock v k _ o U,previous,Finset.mul_sum]
  exact sum_congr rfl (fun i _=>WilsonReportingMeasuredWardIntake.density W Q simple age life _ _ _ o U)

theorem recorded (age:R.family.ref 4 ≤ m) (life:m ≤ N) (clock:ℝ) (v:ℕ→I→ℂ) (k:ℕ):
    let g:=Pert.Asymptotics.regulatorRun R.family N per m
    (∑i:Fin (k+1),
      let q:=WilsonReportingMeasuredWardIntake.charged W Q (per:=per) life 0 (0,submit Q clock v i.val) clock (k-i.val)
      (F).scaled (shrink R.family m N per)
        ((↑(R.family.S.a m^4):ℂ)⁻¹ • Trace.Physical.GermGraph.page (C:=R.family) 4 per m q))=
      intercept Q R clock v k • (F).e0+((g^2:ℝ):ℂ) • coordinates R (0,v k) := by
  intro g
  let a (i:Fin (k+1)):Stock B:=(0,submit Q clock v i.val)
  calc
    _ = ∑ i:Fin (k+1),(scalar R Q (a i) clock (k-i.val) • (F).e0+
          ((g^2:ℝ):ℂ) • coordinates R (projected Q clock (k-i.val) (a i))):=
      sum_congr rfl (fun i _=>WilsonReportingMeasuredWardFixedStock.physical W Q age life (a i) clock (k-i.val))
    _ = _:=rolled Q R ((g^2:ℝ):ℂ) clock v k

end YM.Integration.WilsonReportingMeasuredWardInverse
