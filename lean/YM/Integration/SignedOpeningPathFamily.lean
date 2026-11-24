import YM.Integration.SignedOpeningMarkedVertices
import YM.WilsonCoeffUV.Marked.Step.Exponential

/-! The signed physical source at the opening is the sum of the independently bought fixed-Q
field operators, preserving every source address and projection before nonlinear integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedOpeningPathFamily
open Function Finset Lattice Wilson RG Precision Source Labels Marker Tree Exterior Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily FundedOriginalMarkedInput OriginalSourceJetAddresses
open FreeResolvent Comparison.Density.RenderM PertExtension Series
open scoped Classical BigOperators
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G} {period L n : ℕ} {hn : n ≤ L}
variable {V : Type} [Fintype V] [DecidableEq V]
variable (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R period L n hn V)
variable (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (scale : V → ℂ)
local notation "O" => ActualRunQlocalNativeTuple.orbit D
local notation "d" => OrbitD D
local notation "f" => R.family.side L period
local notation "C" => Stock.census V
local notation "Ix" => SignedOpeningMarkedVertices.Source D u

private def group : Ix ≃ ((i : V) × (Count D u i × (Bool × Bool))) where
  toFun a := ⟨a.1.1.1,((⟨a.1,rfl⟩,a.2.1),a.2.2)⟩
  invFun := fun ⟨_,(⟨⟨s,h⟩,w⟩,q)⟩ => ⟨s,(h.symm ▸ w,q)⟩
  left_inv := by rintro ⟨a,w,q⟩; rfl
  right_inv := by rintro ⟨i,⟨⟨⟨s,h⟩,w⟩,q⟩⟩; subst i; rfl

variable {c : Side} {S : StepData c (R.family.side L period)} {clip : Clip} {path : PathData G} {z : ChartRatio G}
variable (K : Bulk.Kernel S clip path z) (F : Forest S.ratio) (M : Matrix (Woods G (R.family.side L period)) (Woods G c) ℝ)
local notation "ρ" => fderiv ℝ (K.b F) 0
local notation "root₀" => fun i => lift (ActualRunQlocalNativeTuple.root D i)

def panel (x : TestSpace (O)) (q : Bool × Bool) (s : Finset V) : Ink (Active G F ⊕ Woods G c) :=
  SignedMeasuredSourceSeries.probe S F M (ρ)
    (readO (SignedOriginalQCurvatureRows.tests D x (fun _ => q.2))
      (IndependentSourcePathFamily.independent (chosen Q D u μ orders scale (fun _ => q.1)) (root₀) s) (f))

theorem single (x : TestSpace (O)) (i : V) (q : Bool × Bool) :
    panel Q D u μ orders scale K F M x q {i} =
      ∑ b : Count D u i, SignedOpeningSourceCurrent.independent K F M i
        (chosen Q D u μ orders scale (fun _ => q.1) i b)
        (SignedOriginalQCurvatureRows.tests D x (fun _ => q.2)) ((root₀) i) := by
  let X := chosen Q D u μ orders scale (fun _ => q.1)
  let a (b : Count D u i) := X i b
  let E (b : Count D u i) := source (d) i (colour (a b).path (a b).color (a b).weight (a b).quadrant)
    (a b).knob (a b).point (a b).head ((root₀) i)
  have h (b : Count D u i) : WilsonCoeffUV.Mer.Auth 0 (E b) :=
    certified _ _ _ (OriginalMarkedSourceComet.invariant (a b).path (a b).color (a b).weight (a b).quadrant) _ _ _ 0
      (show (a b).rank ≤ 0+(a b).head by simp only [zero_add]; exact le_rfl) _
  let Z := SignedOriginalQCurvatureRows.tests D x (fun _ => q.2)
  unfold panel
  rw [IndependentSourcePathFamily.singleton,show IndependentSourcePathFamily.single X i ((root₀) i)=∑ b,E b from rfl,
    read_Sum (j:=0) Z (f) (fun b _ => h b),_root_.map_sum]
  rfl

theorem dark (q : Bool × Bool) (s : Finset V) (hs : ∀ i, s≠{i}) :
    IndependentSourcePathFamily.independent (chosen Q D u μ orders scale (fun _ => q.1)) (root₀) s=0 := by
  unfold IndependentSourcePathFamily.independent
  exact sum_eq_zero fun i _ => dif_neg (Ne.symm (hs i))

def polynomial (x : TestSpace (O)) (B₀ : fieldDir G c 1) (j : ℕ) (s : (C).Mode) :
    MvPolynomial (Precision.Key F G) ℂ :=
  ∑ i, if s=(C).fire i then ∑ q : Bool × Bool, (phase q.1*phase q.2) •
    SignedRegisteredMarkedProgram.register F B₀ (coeff j (panel Q D u μ orders scale K F M x q {i})) else 0

/-- Exact coefficient, at all original addresses before Wick contraction. Each source has an
independent real or imaginary field weight and an independent real or imaginary spatial test. -/
theorem charged (x : TestSpace (O)) (B₀ : fieldDir G c 1) (j : ℕ) (s : (C).Mode) :
    (∑ a : Ix, SignedOpeningMarkedVertices.multiplier D u s a • SignedRegisteredMarkedProgram.register F B₀
      (coeff j (SignedOpeningMarkedVertices.supplied Q D u μ orders scale K F M x a))) =
      polynomial Q D u μ orders scale K F M x B₀ j s := by
  let base (i : V) (b : Count D u i) (q : Bool × Bool) :=
    SignedOpeningSourceCurrent.independent K F M i (chosen Q D u μ orders scale (fun _ => q.1) i b)
      (SignedOriginalQCurvatureRows.tests D x (fun _ => q.2)) ((root₀) i)
  let H (a : (i : V) × (Count D u i × (Bool × Bool))) :=
    (if s=(C).fire a.1 then phase a.2.2.1*phase a.2.2.2 else 0) •
      SignedRegisteredMarkedProgram.register F B₀ (coeff j (base a.1 a.2.1 a.2.2))
  calc
    _ = ∑ a,H a := Fintype.sum_equiv (group D u) _ _ fun a => rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      unfold polynomial
      apply sum_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]
      by_cases hs : s=(C).fire i
      · simp only [H,hs,if_true]
        rw [sum_comm]
        apply sum_congr rfl
        intro q _
        rw [single,_root_.map_sum,_root_.map_sum,Finset.smul_sum]
      · simp [H,hs]


end YM.Integration.SignedOpeningPathFamily
end
