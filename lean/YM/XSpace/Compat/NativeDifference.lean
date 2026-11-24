import YM.Further.FREE_COVARIANCE_KP.KP.Native

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent Exterior Matrix Precision
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate

def checkin (i:Axis) (f:Cover→ℂ) (x:Cover) := f (x+step i)-f x

def checkout (i:Axis) (f:Cover→ℂ) (x:Cover) := f (x-step i)-f x

end YM.XSpace.Compat.KP
end
