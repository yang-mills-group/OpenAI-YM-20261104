import YM.FVA2.Change.Laurent
import Mathlib.MeasureTheory.Measure.Haar.Basic
/-!
# The identified Wilson prescription input to the matching theorem

At one finite inversion regulator. Geometry `Side` and `Even`; actual group links and Landau
and independent tree weights in FVA2.Laplace. The fields in this prescription are determined by
a single `Dictionary B`, usable for all periods, x, fees, positions and horizons. `M` fixed
coupling reset + regulator mixing before taking MS limit. For attaching open-field conditional
denominator see `YM/FVA2/Handoff.lean`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Change.Dictionary
open Function Set Filter Finset Lattice MeasureTheory
open MS MS.Koszul MS.Plane MS.Book Convolve Program MS.Native MS.Cylinder Lab MS.Menus MS.Rake MS.Local.Physical MS.Fleet MS.Tide MS.Swirl MS.Swirl.Near Slice
variable {G:Gauge} {B:Deck G}{P:LitBook B} {W:Type}
variable (X:Dictionary P)(u:W→Label B)(n:Side)
local notation "E" => Transverse G n
local notation "J" => SiteGhost G n

local instance legFree : Module.Free ℝ (Transverse G n):= Module.Free.of_divisionRing ℝ (Transverse G n)
local instance mapFree : Module.Free ℝ (SiteGhost G n):= Module.Free.of_divisionRing ℝ (SiteGhost G n)
def picked (G:Gauge)(n:Side) := Axes.mk (G:=G) (n:=n) (Module.finBasis ℝ (Transverse G n)) (Module.finBasis ℝ (SiteGhost G n))
private def haus : Measure (Transverse G n):= Measure.addHaar
private instance hw : Measure.IsAddHaarMeasure (haus (G:=G) (n:=n)):= by unfold haus; infer_instance
variable (L:Cover)(d:W→Cover)(ev:Even n.val)
include ev
lemma shifted (l:List (vertices u)) : PertExtension.Series.Tested.Aspiration (fun t:ℝ=> (t⁻¹)^(currency u l) * PertExtension.Orb.preExpectation (joints (X.stage u L d n) l) t) (PertExtension.Series.Tested.term (X.raw u L d n l)):= X.maturity ev u L d (picked G n) (haus n) l
variable [LinearOrder W]
variable (S:Finset W) (M: Land.Prescription B)(x:ℝ)
lemma paired : PhysicalSum G M.team x n true S d L (ApplyM P (Stripped M.team) M u) (X.finite u L d S M n x):= X.call ev u L d (picked G n) (haus n) S M x
/-- Supplier, exact identification including any list of these physical stencils mixed and
changed with the actual re-expression from the MST applications. No conditional hypothesis on the
positive arities. No removal estimate in this theorem. -/
theorem identify {z:ℕ→ℂ}: PhysicalSum G M.team x n true S d L (ApplyM P (Stripped M.team) M u) z ↔ X.finite u L d S M n x=z:= by
    refine ⟨fun h=> classicalμ (τ_nil ..) (X.paired u n L d ev S M x) h,fun k=> k ▸ (X.paired u n L d ev S M x) ⟩
end YM.FVA2.Change.Dictionary
