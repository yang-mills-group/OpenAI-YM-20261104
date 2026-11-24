import YM.Integration.WilsonThermometerFrozenCopies
import YM.Integration.WilsonRegisteredBareMarkedWinding

/-! Declare an independent finite and cover family from the raw inverse-fitted
thermometer before applying either of the two finite Wick steps. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerDeclaredSeeds
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open OriginalMarkedSourceComet IndependentSourcePathFamily WilsonCoeffUV.Winding
open PhysicalNext.Repeat.Legato ActualRunCurvaturePackets NativeCurvatureTensor
open WilsonOriginalStarSceneWords WilsonOriginalStarGradedScene
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
  (d : V→ℕ) (g τ : ℝ) (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ)

abbrev Choice (j : V) := Unit ⊕ WilsonOriginalStarLaurentWallet.Socket R (d j)
def entry (j : V) : Choice R d j → Entry R d
  | .inl _ => .inl j
  | .inr b => .inr ⟨j,b⟩

omit [DecidableEq V] [Fintype V] in
theorem site (j : V) (b : Choice R d j) : root R d (entry R d j b) = j := by cases b <;> rfl

def key : (i : Entry R d) → Fin (rank R d i) → G.ColorIndex
  | .inl _ => Fin.elim0
  | .inr ⟨_,_,z⟩ => fun k=>(word z.val k).2

omit [DecidableEq V] [Fintype V] in
theorem color (i : Entry R d) (w : Fin (rank R d i)→G.ColorIndex) :
    (((raw R d i).coeff w : ℝ):ℂ) = NativeCurvatureTensor.coefficient (key R d i) w := by
  rcases i with j|⟨j,u,b⟩
  · change (1:ℂ) = ∫ k : G.El, ∏ l : Fin 0, _ ∂G.probHaar
    simp
  · exact WilsonOriginalProjectedCurvatureAtom.real _ _

variable {D : V→ℕ} (knob : (j:V)→Knob (D j)) (p : V→Chamber)
  (L : ℂ→L[ℝ]ℝ) (x:T)

def bank (j : V) (b : Choice R d j) : Seed G (D j) :=
  let i := entry R d j b
  { rank := rank R d i, head := rank R d i - pole R d i
    path := (raw R d i).leg, color := key R d i
    weight := t j x*scalar R d g τ v i, quadrant := L, knob := knob j, point := p j }

local notation "B" => bank R d g τ v t knob p L x

omit [DecidableEq V] [Fintype V] in
theorem grade (j : V) (b : Choice R d j) : (B j b).rank ≤ d j + (B j b).head := by
  have h := pole_grade R d (entry R d j b)
  rw [site] at h
  have h₂ := low R d (entry R d j b)
  change rank R d (entry R d j b) ≤ d j + (rank R d (entry R d j b)-pole R d (entry R d j b))
  omega

omit [DecidableEq V] [Fintype V] in
/-- Every color coefficient of the independent seed is the specified real
projection of the same actual frozen socket. -/
theorem coefficient (j : V) (b : Choice R d j) (w : Fin (B j b).rank → G.ColorIndex) :
    (colour (B j b).path (B j b).color (B j b).weight (B j b).quadrant).coeff w =
      L (t j x*scalar R d g τ v (entry R d j b) * ↑((raw R d (entry R d j b)).coeff w)) := by
  change L (_*NativeCurvatureTensor.coefficient (key R d (entry R d j b)) w)=_
  rw [←color R d]
  rfl

/-- These seeds therefore have actual finite and covered coefficients at
every side, subset, homogeneous coupling degree and angular degree. -/
theorem deposited (sites : V → Cover) (s : Finset V) (n : Side) (h a : ℕ) :
    (independent B sites s).1 n h a = plume ((independent B sites s).2 h a) n :=
  WilsonRegisteredBareMarkedWinding.original B sites (grade R d g τ v t knob p L x) s n h a

end YM.Integration.WilsonThermometerDeclaredSeeds
