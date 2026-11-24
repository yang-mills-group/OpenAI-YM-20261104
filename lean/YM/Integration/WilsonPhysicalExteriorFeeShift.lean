import YM.Integration.WilsonPhysicalExteriorSlotReference
import YM.Integration.MSFeeCoordinates

/-! An all-orders coordinate change for the original, presold finite fee
rows at two distinct subtraction arguments. Each resulting coefficient
acts on the old prescription's own Wilson glyphs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFeeShift
open Finset Matrix Polynomial MS MS.Land MS.Menus MS.Rake
open FVAAlt2 FVAAlt2.Billing FVAAlt2.Lobby MSFeeCoordinates
open scoped Classical BigOperators
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{d:ℕ}
local notation "PS" => PowerSeries ℂ
variable (Q:Prescription B)

def scalar (y:ℝ) : MSFeeCoordinates.R →+* PS :=
  (PowerSeries.map Complex.ofRealHom).comp (MSFeeCoordinates.evaluate y)

def frame (d:ℕ) (y:ℝ) : Matrix (Glyph B d) (Glyph B d) PS :=
  (scalar y).mapMatrix (MSFeeCoordinates.matrix Q d)

def oldFrame (d:ℕ) (y:ℝ) : Matrix (Glyph B d) (Glyph B d) PS :=
  (scalar y).mapMatrix (MSFeeCoordinates.matrix Q d)⁻¹

def change (d:ℕ) (v y:ℝ) : Matrix (Glyph B d) (Glyph B d) PS :=
  frame Q d v * oldFrame Q d y

private theorem solved (d:ℕ) (v y:ℝ) : change Q d v y*frame Q d y=frame Q d v := by
  have h : oldFrame Q d y*frame Q d y=1 := by
    rw [oldFrame,frame,←map_mul,Matrix.nonsing_inv_mul _ (MSFeeCoordinates.determinant Q d),map_one]
  rw [change,Matrix.mul_assoc,h,Matrix.mul_one]

theorem coefficients (v y:ℝ) (a b:Glyph B d) :
    ∑ i,change Q d v y a i*frame Q d y i b=frame Q d v a b :=
  congrFun (congrFun (solved Q d v y) a) b

theorem identity (d:ℕ) (y:ℝ) : change Q d y y=1 := by
  rw [change,frame,oldFrame,←map_mul,Matrix.mul_nonsing_inv _ (MSFeeCoordinates.determinant Q d),map_one]

private theorem stored (A:Acts B d) (j:Glyph B d) (y:ℝ) :
    scalar y (MSFeeCoordinates.register A j)=PowerSeries.mk (fun k=>oil A j k y) := by
  apply PowerSeries.ext;intro k
  simp [scalar,MSFeeCoordinates.evaluate,MSFeeCoordinates.register,PowerSeries.coeff_map,oil]

def fee (p:Label B) (y:ℝ) (j:Glyph B p.h) : PS :=
  PowerSeries.mk (fun k=>oil (Q.fees p.h p.item) j k y)

theorem padded (y:ℝ) (a:Glyph B d) (j:Glyph B a.size) :
    frame Q d y a (MSFeeCoordinates.extend (remaining a) j)=fee Q (owner a) y j := by
  change scalar y (packet (remaining a) (Q.fees a.size a.2) (MSFeeCoordinates.extend _ j))=_
  rw [packet_extend]
  exact stored _ _ _

theorem outside (y:ℝ) (a b:Glyph B d) (h:a.size < b.size) : frame Q d y a b=0 := by
  change scalar y (packet (remaining a) (Q.fees a.size a.2) b)=0
  rw [packet,dif_neg (not_le.mpr h),map_zero]

theorem held (p:Label B) (v y:ℝ) (j:Glyph B p.h) :
    ∑ i,change Q p.h v y (Land.read p.item) i*frame Q p.h y i j=fee Q p v j := by
  rw [coefficients]
  exact padded Q v (Land.read p.item) j

end YM.Integration.WilsonPhysicalExteriorFeeShift
end
