import YM.Integration.WilsonPointChildFiniteReturn
import YM.Integration.WilsonMarkedIndependentNormalizedTop
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildEra
open Function Filter Matrix Finset Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}{k:ℕ}

/-- These two substitutions use the same power series and the identical
derivatives of the original analytic chart. -/
theorem train {U I:Type} (y:U→Ink I):Blue.train y=Wick.roam ℝ y:=by
  apply Blue.serial_ext
  · rw [Blue.train_X,constantCoeff_X]
  · intro a;rw [Blue.train_C,Wick.roam,Series.change_C];rfl
  · rw [Blue.train_X,Wick.roam,Series.change_X]

theorem axes {I U:Type} [Fintype I] [DecidableEq I] (f:Rays I→Rays U):Blue.spool f=Jets.motor f:=by
  funext i
  apply PowerSeries.ext
  intro e
  simp only [Blue.spool,Jets.motor,Jets.afterX,coeff_mk,WilsonVacuumPreResetIndependentBirth.germ,Nat.add_comm 1 e]

/-- Recover the coefficient Ward test from a finite nonlinear Ward identity.
The gauge is constant at zero because the actual transformed flat links
force equality at the two ends of every bond. -/
theorem nonlinear {P Q:Pap (wire G n)}{s:Signed}{b:Site n}(h:Rite P Q s b):rollTest P Q s b:=by
  intro I inst q a c pair
  have flat:∃g:G.El,q 0=fun _=>g:=⟨q 0 0,funext fun t=>sail_root s b pair t 0⟩
  have transformed:=h I a c q pair.f₀ pair.f₁ pair.g₀ pair.g₁ pair.gauge flat
    (by simpa only [WilsonCoeffUV.Bank.Mosaic.mantle_input] using pair.shift)
  rwa [train,train,axes,axes]

/-- A whole power series of the dated fixed-child matrix acts simultaneously
on the true finite and covered sources, with its full signed convolution. -/
def funded (A:Cost)(X:Era G ℝ):Era G ℝ:=(fun n=>affix A (X.1 n),affix A X.2)

private theorem push {U:Type}(t:ℝ→ₗ[ℝ]ℝ)(A:Cost)(X:Pal ℝ U):ply t (affix A X)=affix A (ply t X):=by
  funext i r x
  simp only [ply_v,affix,Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]

theorem checked {X:Era G ℝ}(h:Auth k X)(A:Cost):Auth k (funded A X):=by
  refine ⟨?_,fun n=>affix_shell A _ (h.span n),fun n=>aspire _ _ (h.pale n),?_⟩
  · intro e r
    simp_rw [funded,affix,Finset.sum_apply]
    exact anzas (P:=fun (j:ℕ×ℕ) n=>coeff j.1 A • X.1 n j.2 r) _
      (fun j _=>(h.wing j.2 r).μ _)
  · intro n t I inst q a c pair
    have cap:=ply_shell t (h.span n)
    change Blue.train _ (flash (ply t (affix A (X.1 n))))=Blue.train _ (flash (ply t (affix A (X.1 n))))
    rw [push,sponsor _ _ cap,map_mul,map_mul,Blue.income,Blue.income,h.token n t pair]

end YM.Integration.WilsonPointChildEra
