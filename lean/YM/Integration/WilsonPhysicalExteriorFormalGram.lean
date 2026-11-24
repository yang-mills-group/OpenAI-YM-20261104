import YM.Integration.MSDeckProbeGram
import YM.Integration.MSExteriorFiniteScales

/-! The formal inverse of the actual independent MS two-point rows at far positions.
All orders and all named fields in the finite physical horizon use the same matrix.
Only the exterior slot is rescaled before the inverse, leaving one engineering factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFormalGram
open Function Matrix Pert Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open FVA2 FVA2.ColorCode OPE.Levy Extra.FD
open scoped Classical BigOperators

variable {G : Gauge} (V : Warehouse G) {B : MS.Local.Physical.Deck G} {A : Booked B}
variable (M : MS_Data G A) (h : ℕ) (p q : E4)
local notation "I" => Glyph B h
local notation "𝒦" => Matrix I I ℂ

def matrix (μ : ℝ) : PowerSeries 𝒦 :=
  PowerSeries.mk (MSDeckProbeGram.matrix M h p q μ)

def tree (hp : p≠q) : 𝒦ˣ := (MSDeckProbeGram.invertible V M 0 hp h).unit

theorem bottom (hp : p≠q) (μ : ℝ) :
    PowerSeries.constantCoeff (matrix M h p q μ) = (tree V M h p q hp : 𝒦) := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,matrix,PowerSeries.coeff_mk,
    tree,IsUnit.unit_spec]
  ext a b
  rw [MSDeckProbeGram.free_entry V M μ hp,MSDeckProbeGram.free_entry V M 0 hp]

def inverse (hp : p≠q) (μ : ℝ) : PowerSeries 𝒦 :=
  (matrix M h p q μ).invOfUnit (tree V M h p q hp)

def charge (s : ℝ) (a : Glyph B h) : ℂ := MSExteriorDilation.power a.size s
def gear (s : ℝ) : 𝒦 := Matrix.diagonal (charge (B:=B) h s)

private theorem turns (s : ℝ) : gear (B:=B) h s * gear h (-s) = 1 := by
  rw [gear,gear,Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one]
  congr 1
  funext a
  change ((Real.exp ((a.size:ℝ)*s):ℝ):ℂ)*((Real.exp ((a.size:ℝ)*(-s)):ℝ):ℂ)=1
  norm_cast
  rw [←Real.exp_add]
  simp

def word (a b : Glyph B h) : Fin 2 → Label B := FVA2.ColorCode.labelAt B ∘ ![a,b]
def place (s : ℝ) : Fin 2 → QP := MSExteriorDilation.stretch s (Fountain.metric (couple p q))

/-- These are the original two measured correlation slots at exp(s) times each
position. The probed exterior's canonical charge is supplied, the inner charge is not. -/
def far (μ s : ℝ) : PowerSeries 𝒦 :=
  PowerSeries.mk (fun k a b => charge h s b * Dial.tour M (word h a b) μ (place p q s) Finset.univ k)

private theorem grades (a b : Glyph B h) : MSExteriorDilation.weight (word h a b) = a.size+b.size := by
  rw [MSExteriorDilation.weight,Fin.sum_univ_two]
  rfl

theorem rows (hp : p≠q) (μ s : ℝ) :
    far M h p q μ s = PowerSeries.C (gear (B:=B) h (-s)) * matrix M h p q (μ+s) := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_C_mul,matrix,PowerSeries.coeff_mk,far,PowerSeries.coeff_mk]
  ext a b
  rw [gear,Matrix.diagonal_mul]
  let z := Fountain.metric (couple p q)
  have hx : Injective z := Fountain.metric_conf (couple_ok hp)
  have sc := MSExteriorDilation.scales M (word h a b) (μ+s) s z hx k
  rw [add_sub_cancel_right,grades,Nat.cast_add] at sc
  change charge h s b * MSExteriorDilation.moment M (word h a b) μ (MSExteriorDilation.stretch s z) k =
    charge h (-s) a * MSExteriorDilation.moment M (word h a b) (μ+s) z k
  rw [sc,←mul_assoc]
  congr 1
  unfold charge MSExteriorDilation.power
  norm_cast
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The exact decoder has the complete independently booked inverse at log μ+s,
followed by precisely one diagonal engineering rescaling of the output. -/
def decoder (hp : p≠q) (μ s : ℝ) : PowerSeries 𝒦 :=
  inverse V M h p q hp (μ+s) * PowerSeries.C (gear (B:=B) h s)

theorem correct (hp : p≠q) (μ s : ℝ) :
    far M h p q μ s * decoder V M h p q hp μ s = 1 ∧
    decoder V M h p q hp μ s * far M h p q μ s = 1 := by
  let X := matrix M h p q (μ+s)
  let Y := inverse V M h p q hp (μ+s)
  have hxy : X*Y=1 := PowerSeries.mul_invOfUnit _ _ (bottom V M h p q hp (μ+s))
  have hyx : Y*X=1 := PowerSeries.invOfUnit_mul _ _ (bottom V M h p q hp (μ+s))
  have hs := turns (B:=B) h s
  have hs' : gear (B:=B) h (-s)*gear h s=1 := by simpa only [neg_neg] using turns (B:=B) h (-s)
  rw [rows M h p q hp,decoder]
  change PowerSeries.C (gear h (-s))*X*(Y*PowerSeries.C (gear h s))=1 ∧
    Y*PowerSeries.C (gear h s)*(PowerSeries.C (gear h (-s))*X)=1
  constructor
  · rw [mul_assoc,←mul_assoc X, hxy,one_mul,←map_mul,hs',map_one]
  · rw [mul_assoc,←mul_assoc (PowerSeries.C (gear h s)),←map_mul,hs,map_one,one_mul,hyx]

end YM.Integration.WilsonPhysicalExteriorFormalGram
end
