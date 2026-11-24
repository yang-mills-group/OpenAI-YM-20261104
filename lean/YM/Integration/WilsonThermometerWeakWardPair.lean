import YM.Integration.WilsonThermometerWeakWardReading

/-! The signed finite projected difference heard by the actual second cell in
the weak thermometer determinant, with the original Haar erasure and UV price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardPair
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat Legato Bandage Cells Next.UVStress RG05Readout RG05Readout.Address
open WilsonOffsetReportingProducts WilsonOffsetEquationLaw WilsonAddressedCollarEquations WilsonAddressedEquationShelf
open WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField WilsonThermometerRelativeWard WilsonThermometerWeakEquationCost
open WilsonThermometerWeakWardReading
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
private theorem pair {N p:ℕ} (T:Tiling ((C).side N p)) (cols:Fin 2→Site T.period)
    (apart:cols 0≠cols 1) (fields:Fin 2 → (Config G ((C).side N p)→ℂ))
    (inside:∀i,Interior (T.chamber 0) (fields i)):
    ‖moment ((C).beta N p) (fun U=>T.copy (cols 0) (fields 0) U*T.copy (cols 1) (fields 1) U)‖≤
      T.rootTest ((C).beta N p) (fields 0)*T.rootTest ((C).beta N p) (fields 1):=by
  have distinct:Injective cols:=by intro i j eq;fin_cases i<;>fin_cases j<;>simp_all
  have seen:=T.planted (seamless R.makes N p) cols distinct fields inside
  simp only [Fin.prod_univ_two] at seen
  exact seen

variable (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)) (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (issued:Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))
include W portfolio issued

theorem original (simple:G.Simple) (d:ℕ) : ∃ radius:ℕ,∀ᶠ k:ℕ in atTop,∀ᶠ N:ℕ in atTop,
    ∃ h:k≤N,∀ (p m:ℕ) (prior:m≤k) (v u:Site ((C).side m p)) (_:v≠u) (o:Site ((C).side N p)),
    let T:=center (C).S p (prior.trans h) 0
    o∈T.margin v (3*span (C).S h p) → ∀ (Z X:Config G ((C).side N p)→ℂ) (test:Continuous X),
    LocalOn (Mark.Outer radius o) X → T.copy u Z=X → Interior (T.chamber 0) Z →
    ∀ (sites:∀j,Bud C p j) (B:ℕ→ℕ→ℝ) (A:Sight C d p) (r:Emblems C d),
    Enrolled R.makes R.doors B k N p d sites A r → ∀ (x:(C).label d) (y:Palette C d),
    b.step d (N,p) x=b.step d (N,p) (column R (p:=p) r h y) →
    ‖read R d N p o X test x - read R d N p o X test (column R (p:=p) r h y)‖≤
      (2*(Fintype.card ((C).labels.level d).Index*‖x‖+size y))*
      Real.exp (-(3/128:ℝ)*(C).S.scale N)*T.rootTest ((C).beta N p) Z:=by
  obtain ⟨radius,identity⟩:=WilsonThermometerWeakWardReading.original R V W P b portfolio issued d
  refine ⟨radius,?_⟩
  filter_upwards [WilsonThermometerRelativeWard.paid R V W P b portfolio issued simple d,
    WilsonThermometerWeakEquationCost.original R P issued d (1/128) (by norm_num)] with k cells charges
  filter_upwards [cells,charges,identity] with N inspected before heard
  obtain ⟨h,issuedCell⟩:=inspected
  refine ⟨h,?_⟩
  intro p m prior v u apart o T margin Z X test away copied inside sites B A r seat x y same
  let Y:=column R (p:=p) r h y
  obtain ⟨D,cleared,tariff,id⟩:=issuedCell p x Y prior v o margin
  have capped:=before p h sites B A r seat x y
  let cols:Fin 2→Site T.period:=![v,u]
  let fields:Fin 2→(Config G ((C).side N p)→ℂ):=![D,Z]
  have house (i:Fin 2):Interior (T.chamber 0) (fields i):=by fin_cases i;exact cleared;exact inside
  have paid:=pair R T cols apart fields house
  have cash:T.rootTest ((C).beta N p) D≤(2*(Fintype.card ((C).labels.level d).Index*‖x‖+size y))*
      Real.exp (-(3/128:ℝ)*(C).S.scale N):=by
    calc
      _ ≤ _ := tariff
      _ ≤ _ := mul_le_mul_of_nonneg_right capped (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring
  rw [heard p o X test away x Y same]
  apply le_trans _ (mul_le_mul_of_nonneg_right cash (T.root_nonneg _ _))
  change ‖moment ((C).beta N p) (fun U=>T.copy v D U*T.copy u Z U)‖≤T.rootTest ((C).beta N p) D*T.rootTest ((C).beta N p) Z at paid
  rwa [id,copied] at paid

end YM.Integration.WilsonThermometerWeakWardPair
end
