import YangMills.Wightman
import YangMills.WilsonProof.NativeSupport.YangMills.Geometry

/-! Smeared quantum fields, spacetime symmetry and the Wightman axioms. -/
set_option autoImplicit false

noncomputable section

namespace YangMills

open MeasureTheory Set Function
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius








/-! ## Basic quantum-field structures -/


attribute [instance] HilbertSpace.normedAddCommGroup
attribute [instance] HilbertSpace.innerProductSpace
attribute [instance] HilbertSpace.completeSpace

namespace HilbertSpace


end HilbertSpace


attribute [instance] FieldLabels.addCommGroup
attribute [instance] FieldLabels.module


namespace FieldSystem

variable {H : HilbertSpace} {Labels : FieldLabels}








end FieldSystem

/-! ## Translations, spectrum, and Poincaré covariance -/



namespace EnergyMomentumMeasure

attribute [instance] finite

end EnergyMomentumMeasure




attribute [instance] PoincareAction.one
attribute [instance] PoincareAction.mul
attribute [instance] PoincareAction.topology

/-! ## Wightman axioms W0–W3 -/


namespace WightmanTheory

variable {H : HilbertSpace} {Labels : FieldLabels}






end WightmanTheory

end YangMills

end
