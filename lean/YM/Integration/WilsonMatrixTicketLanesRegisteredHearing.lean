import YM.Integration.WilsonInvariantActionRegisteredHearing
import YM.Integration.WilsonInvariantActionCapturedProfile

/-! The complete signed interest of a rooted variation on the occupied two-site
test, with both vacuum means and the genuine previous law at every placement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredHearing
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot OPE.Therm FullVolume Table
open PhysicalNext.Repeat.Legato WilsonInvariantActionPriorHearing WilsonInvariantActionRegisteredHearing
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {k N per:ℕ}
local notation "upper" => Config G (R.family.side (k+1) per)
local notation "lower" => Config G (R.family.side k per)
local notation "Ω" => (lower×upper)
local notation "Sites" => (Fin 2 → Site (R.family.side N per))
local notation "Re" => Complex.reCLM
local notation "Im" => Complex.imCLM

/-- Keep the complex spatial weight outside both covariance centers. -/
def channel (χ:ℂ →L[ℝ]ℝ) (w:ℂ) (u:(ℂ →L[ℝ]ℝ) → (ℂ →L[ℝ]ℝ) → ℝ):ℝ:=
  χ w*(u Re Re-u Im Im)+χ (w*Complex.I)*(u Re Im+u Im Re)

def panel (live:k<N) (birth:R.family.ref 4 ≤ k+1) (v:Fin 2 → R.family.label 4) (φ:Test 2) (χ:ℂ →L[ℝ]ℝ)
    (K:Sites → readings Ω → readings Ω → ℝ):ℝ:=
  ∑x:Sites,let a:=fun i=>(R.family.S.toDepth live per).parent (x i)
    channel χ (WilsonExternalMeshMass.charge R.family φ x)
      (fun η θ=>K x (filed R live birth (v 0) (a 0) η) (filed R live birth (v 1) (a 1) θ))

def variation (inside:k+1<N) (birth:R.family.ref 4 ≤ k+1) (v:Fin 2 → R.family.label 4) (φ:Test 2)
    (χ:ℂ →L[ℝ]ℝ) (numerator:Sites → readings Ω) (t:ℝ):ℝ:=
  let live:k<N:=Nat.lt_trans (Nat.lt_succ_self k) inside
  panel R live birth v φ χ fun x=>covariance (reweighted (joint R (p:=per) live) (score R inside (numerator x)) t)

def incomes (inside:k+1<N) (birth:R.family.ref 4 ≤ k+1) (v:Fin 2 → R.family.label 4) (φ:Test 2)
    (χ:ℂ →L[ℝ]ℝ) (numerator:Sites → readings Ω):ℝ:=
  let live:k<N:=Nat.lt_trans (Nat.lt_succ_self k) inside
  panel R live birth v φ χ fun x A B=>receipts R live A B (score R inside (numerator x))

theorem derivative (inside:k+1<N) (birth:R.family.ref 4 ≤ k+1) (v:Fin 2 → R.family.label 4) (φ:Test 2)
    (χ:ℂ →L[ℝ]ℝ) (numerator:Sites → readings Ω):
    HasDerivAt (variation R inside birth v φ χ numerator) (incomes R inside birth v φ χ numerator) 0:=by
  let live:k<N:=Nat.lt_trans (Nat.lt_succ_self k) inside
  unfold variation incomes panel
  apply HasDerivAt.fun_sum
  intro x _
  let a:=fun i=>(R.family.S.toDepth live per).parent (x i)
  have arm (η θ:ℂ →L[ℝ]ℝ):=registered R inside birth (v 0) (v 1) (a 0) (a 1) η θ (numerator x)
  let w:=WilsonExternalMeshMass.charge R.family φ x
  exact (((arm Re Re).sub (arm Im Im)).const_mul (χ w)).add (((arm Re Im).add (arm Im Re)).const_mul (χ (w*Complex.I)))

/-- Each selected prior occurrence retains every compatible partner and its complete
signed positive-vacuum division at its own original cutoff. -/
theorem rooted (inside:k+1<N) (birth:R.family.ref 4 ≤ k+1) (v:Fin 2 → R.family.label 4) (φ:Test 2)
    (χ:ℂ →L[ℝ]ℝ) (i:Sites → ℕ):
    HasDerivAt (variation R inside birth v φ χ (fun x=>hard R (p:=per) inside (i x)))
      (incomes R inside birth v φ χ (fun x=>hard R (p:=per) inside (i x))) 0:=
  derivative R inside birth v φ χ _

end YM.Integration.WilsonMatrixTicketLanesRegisteredHearing
