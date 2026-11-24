import YM.Integration.WilsonPhysicalExteriorReceivedGerms
import YM.Integration.MSFiniteReceiverMatrix

/-! Split the genuine rectangular Wilson experiment at its last
engineering grade, with all bulk reparametrizations kept intact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorGradeReadout
open Function Matrix Finset Filter PowerSeries Lattice
open MS MS.Land MS.Rake MS.Menus MS.Dial MS.Tide
open PhysicalNext.Repeat.Legato FVAAlt2 Lobby Precision RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorFieldGram WilsonPhysicalExteriorPairedLimit WilsonPhysicalExteriorReceivedGerms
open scoped Classical BigOperators
variable {G:Gauge}{B:MS.Local.Physical.Deck G}
variable (R:Run G) (Q:Prescription B) (T:Trial ℕ (Fin 2))
local notation "PS" => PowerSeries ℂ

def step (h:ℕ) (μ ν:ℝ) (i:ℕ) : Matrix (Glyph B h) (Glyph B h) PS :=
  change Q h (μ-T.profile.θ i) (ν-T.profile.θ i) (spacing T i)
def lower (h:ℕ) (μ ν:ℝ) (i:ℕ) : Matrix (Plaid B (h+1)) (Glyph B h) PS :=
  (step Q T (h+1) μ ν i).submatrix Land.read (MSFeeCoordinates.extend (Nat.le_succ h))
def boundary (h:ℕ) (μ ν:ℝ) (i:ℕ) : Matrix (Plaid B (h+1)) (Plaid B (h+1)) PS :=
  (step Q T (h+1) μ ν i).submatrix Land.read Land.read
def edge (h:ℕ) (ν:ℝ) (i:ℕ) : Matrix (Plaid B (h+1)) (Glyph B h) PS :=
  (observed R Q T (h+1) h ν i).submatrix Land.read id
def inner (h:ℕ) (μ ν:ℝ) (i:ℕ) : Matrix (Plaid B (h+1)) (Glyph B h) PS :=
  (transported R Q T (h+1) h μ ν i).submatrix Land.read id

theorem square (h:ℕ) (μ ν:ℝ) (i:ℕ) :
    observed R Q T h h ν i =
      step Q T h μ ν i * transported R Q T h h μ ν i * (step Q T h μ ν i).transpose :=
  rectangular R.metals.O (basisR R) Q h h (μ-T.profile.θ i) (ν-T.profile.θ i) (spacing T i)
    (Real.exp_pos _).ne' (situated T i)

private theorem split (h:ℕ) (μ ν:ℝ) (i:ℕ) (b:Plaid B (h+1)) (c:Glyph B h) :
    (step Q T (h+1) μ ν i * transported R Q T (h+1) h μ ν i) (Land.read b) c =
    ((lower Q T h μ ν i * transported R Q T h h μ ν i)+(boundary Q T h μ ν i * inner R Q T h μ ν i)) b c := by
  rw [Matrix.mul_apply,MSFiniteReceiverMatrix.window_sum h]
  rfl

theorem outlet (h:ℕ) (μ ν:ℝ) (i:ℕ) :
    edge R Q T h ν i =
      (lower Q T h μ ν i * transported R Q T h h μ ν i +
        boundary Q T h μ ν i * inner R Q T h μ ν i) * (step Q T h μ ν i).transpose := by
  have go:observed R Q T (h+1) h ν i =
      step Q T (h+1) μ ν i * transported R Q T (h+1) h μ ν i * (step Q T h μ ν i).transpose :=
    rectangular R.metals.O (basisR R) Q (h+1) h (μ-T.profile.θ i) (ν-T.profile.θ i) (spacing T i)
      (Real.exp_pos _).ne' (situated T i)
  apply Matrix.ext;intro b c
  change observed R Q T (h+1) h ν i (Land.read b) c=_
  rw [go,Matrix.mul_apply,Matrix.mul_apply]
  apply sum_congr rfl;intro a _
  rw [split R Q T h μ ν i b a]

end YM.Integration.WilsonPhysicalExteriorGradeReadout
end
