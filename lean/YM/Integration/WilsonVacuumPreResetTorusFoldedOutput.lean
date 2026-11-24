import YM.Integration.WilsonVacuumPreResetTorusFundedConditional
import YM.Integration.RootedVacuumWinding

/-! The centered one-step vacuum on the physical side against the finite output
in the original all-side winding estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusFoldedOutput
open Function Finset Filter Lattice Wilson RG RG.Supply Precision Tree Exterior Matrix Bloch
open Pressure PhysicalNext.Repeat.Legato FreeResolvent PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Fk WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Mer WilsonCoeffUV.Winding
open scoped BigOperators Classical
variable {G:Gauge}

private abbrev stepAt (P:Patch) (K:KernelChoices) (n:Side):StepData n (n*P.L):=⟨P,K,rfl⟩

private theorem transport {n f:Side} (S:StepData n f) (P:Patch) (K:KernelChoices)
    (hp:S.patch=P) (hk:S.kernel=K) (u:PoleRows S.patch) (v:PoleRows P) (row:HEq u v)
    (H Y:FaceRow) (O:ChartRatio G) (U:Crude G):
    winter S (repeatF S) H Y (installed S.ratio u) O (U f)=
      winter (stepAt P K n) (repeatF (stepAt P K n)) H Y
        (installed (stepAt P K n).ratio v) O (U (n*P.L)):=by
  rcases S with ⟨p,k,hs⟩
  change p=P at hp
  change k=K at hk
  subst p
  subst k
  replace hs:f=n*P.L:=Subtype.ext hs
  subst f
  replace row:u=v:=eq_of_heq row
  subst u
  rfl

def difference {Y:Type*} (f:Ink Y) (t:ℕ)(x y:Lawn Y) : ℝ :=
  MvPolynomial.eval x (coeff t f)-MvPolynomial.eval y (coeff t f)

/-- After the coarse classical quadratic is removed, the original forest's normalized
log has the opposite sign to the finite output. The scalar normalization cancels
between the two complete evaluations. -/
theorem original (R:Run G)(simple:G.Simple)(N i per:ℕ)(live:i<N):
    let A:=R.family.path.levels
    let S:=A.clock.op i per
    let H:=freeForms A N (i+1)
    let Y:=freeForms A N i
    let n:=R.family.side i per
    let f:=R.family.side (i+1) per
    let input:=emera (actionW A R.metals.O N (i+1))
    let M:=installed S.ratio (predictionA A N i)
    ∀t x y,difference (logOf (inside S (repeatF S) H M R.metals.O (input f))) t x y-
      difference (orbC (precisionC G n Y)) t x y =
        -difference (Blue.flash (coil0 A R.metals.O i N n)) t x y:=by
  intro A S H Y n f input M t x y
  have pres:coil0 A R.metals.O i N n=winter S (repeatF S) H Y M R.metals.O (input f):=
    (transport S (loose A i) A.clock.kernel rfl rfl (predictionA A N i) (predictionA A N i)
      HEq.rfl H Y R.metals.O input).symm
  have shape:=emera_far A simple R.alloy.B.ratio live f
  have rd:=winter_read S (repeatF S) H Y M shape.1 R.alloy.B.ratio (A.blocks i per).branches
    (age_sym A N (i+1) f) shape.2
  rw [pres,rd]
  simp only [difference,map_sub,map_add,soil,coeff_map,MvPolynomial.eval_C]
  abel

end YM.Integration.WilsonVacuumPreResetTorusFoldedOutput
