import YM.Integration.WilsonThermometerOriginalCylinder

/-! Finite-cutoff qualification of the entire compensated thermometer for
the original Wilson reporting hierarchy at arbitrary microscopic sites. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerBornCredit
open Filter Function Finset Set Lattice Wilson RG Source Labels Marker Push.Local
open Extra.Histories FVA1 PhysicalNext.Repeat.Legato Next.Rank Next.UVStress RG16.Literal
open WilsonPositionThermometerCapStation WilsonThermometerCenteredAlgebra WilsonThermometerLiteralCredit
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "J" => Stock.census (Fin 3)
local notation "W" N:max p:max => R.family.path.rep N p N
local notation "S" => R.family.localSection 0

include simple in
/-- The upper source is literally booked on the original hard inventory. Its
finite cost can depend on the cutoff, period and independent sites. -/
theorem original : ∀ᶠ N : ℕ in atTop, ∀ (per : ℕ) (A : Group C 6)
    (o : Positions (Fin 3) (R.family.side N per)) (y : Site (R.family.side N per)) (Q : Poly J),
    ∃ (cost : ℝ) (q : Coefficient (F) (R.family.side N per)), 0≤cost ∧
      q.Format y (C).params (W N per) ∧ q.remBound y (W N per) (LocalComparison.forcedDivisor C N) cost ∧
      (F).coeffSize q.x ≤ cost ∧ (∀ U,q.density y (S) (W N per) U=((W N per).eval U:ℂ)*cut R A o Q U) ∧
      credit C N per 0 (cut R A o Q) N le_rfl = q.density y (S) (W N per) := by
  filter_upwards [WilsonThermometerOriginalCylinder.original R simple] with N bought
  intro per A o y Q
  let rad:=Finset.univ.sup (fun j:Fin 3=>separation (o.origin j) y)
  choose E covers using (fun s:(J).Mode=>isCompact_univ.exists_bound_of_continuousOn
    (WilsonThermometerLiteralCredit.continuous_face R A o s).continuousOn)
  obtain ⟨q,shape,paid,size,density,credited⟩:=bought per A o y Q rad (fun j=>le_sup (f:=fun j:Fin 3=>separation (o.origin j) y) (mem_univ j))
    E (fun s U=>covers s U (mem_univ U))
  let fee := ∑ s : (J).Mode, ‖weight Q s‖*WilsonThermometerBareStore.fee R A o s y
    (LocalComparison.forcedDivisor C N) (E s) (Next.Foundations.price G
      (max (W N per).p.order (W N per).p.power)) rad
  exact ⟨max fee ((F).coeffSize q.x),q,(by unfold Labels.Frame.coeffSize;positivity:
    0≤(F).coeffSize q.x).trans (le_max_right ..),shape,rem_mono paid (le_max_left ..),
    le_max_right ..,density,credited⟩

end YM.Integration.WilsonThermometerBornCredit
