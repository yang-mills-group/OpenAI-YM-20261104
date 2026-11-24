import YM.Integration.WilsonIndependentSpoutNormalizedMaster

/-! The normalized master is semilinear in its inherited public coordinates at the actual source clock. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterCoordinates
open Lattice Wilson RG Source Labels XSpace Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Mer WilsonCoeffUV.Power
open WilsonPositionProgramTrialReverseLens (received)
open scoped Classical BigOperators
variable {G:Gauge}(A:Levels G)(O:ChartRatio G)(Q:SealR G)

def axis (a:Alma Q.F):Q.Rider:=fun j=>if j=a then 1 else 0

theorem inverse (N m:ℕ)(a j:Alma Q.F):
    PermuteLens A O Q N m (axis Q a) j=PowerSeries.C ((Wray A O Q.ans Q.path N m)⁻¹ j a):=by
  classical
  simp [PermuteLens,axis,PowerSeries.smul_eq_C_mul]

theorem intake (N m:ℕ)(b:Q.Rider)(j:Alma Q.F):
    PermuteLens A O Q N m b j=∑a,b a*PermuteLens A O Q N m (axis Q a) j:=by
  simp only [inverse A O Q N m]
  simp only [PermuteLens,PowerSeries.smul_eq_C_mul,mul_comm]

theorem original (N m K:ℕ)(b:Q.Rider)(j:Alma Q.F):
    received A O Q m K N b j =
      ∑a,reel (relativeC A O N m (K-m)) (b a)*received A O Q m K N (axis Q a) j:=by
  classical
  let M:=bindingS A O Q.ans Q.path N m (K-m) false
  let α:=reel (relativeC A O N m (K-m))
  change α (∑i,M j i*PermuteLens A O Q N m b i)=
    ∑a,α (b a)*α (∑i,M j i*PermuteLens A O Q N m (axis Q a) i)
  simp_rw [←map_mul]
  rw [←map_sum]
  apply congrArg α
  simp_rw [intake A O Q N m b,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun i _=>by ring
end YM.Integration.WilsonIndependentSpoutMasterCoordinates
end
