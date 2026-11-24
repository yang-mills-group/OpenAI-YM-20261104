import YM.MS.Wilson.LieWords
import YangMills.WilsonProof.NativeSupport.YM.MS.Wilson.Space
import YM.MS.Color.Only

/-!
# Bracket at lattice sites (no unimodular basis choice required)

Actually use orthonormal frame of real compact group, no compactness of whole site space needed.
    Quantization: retained through ghosts on exact stencils too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native
open Function Filter Finset Set Koszul Plane Lattice Cylinder Taylor Complex
open scoped Topology ContDiff InnerProductSpace
variable {G: Gauge}{P : Type} [DecidableEq P] [Fintype P]

-- physical closure coefficients table for single site. f abc (left bracket)

local notation "κ" => colorTerm G P
end YM.MS.Native
