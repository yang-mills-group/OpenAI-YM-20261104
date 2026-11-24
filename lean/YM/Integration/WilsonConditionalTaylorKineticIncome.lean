import YM.Integration.WilsonConditionalTaylorFiniteHessian
import YM.Integration.WilsonConditionalTaylorSceneReset
import YM.Integration.WilsonConditionalTaylorCaliperPayment
import YM.Integration.WilsonRunMarkedKineticComparison

/-! The signed primitive discrepancy at every positive perturbative order
is the finite two-field moment minus its separately computed cover moment,
with the true measured kinetic denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorKineticIncome

open Function PowerSeries Lattice RG Wilson Precision MSbar MSbar.Heath MSbar.Midpoint MSbar.Wave
open MSbar.Cacao FormalBulk08 FormalBulk08.City FormalBulk08.Orb FormalBulk08.Lava
open FormalBulk08.Bank FormalBulk08.Cork FormalBulk08.Dove PhysicalNext.Repeat.Legato
open Qlocal.Schedule WilsonConditionalTaylorSceneCalibration WilsonConditionalTaylorKineticRebooking
open AnalyticBridge.VerifiedReset (coord)
open Push.Uniform Next.Free FormalBulk08.Flat
open scoped Classical BigOperators

variable {G : Gauge} {c : Side}

def finite (P : MvPolynomial (Primary c G) ℝ) (u : G.ColorIndex) : ℝ :=
 (Fintype.card (Site c):ℝ)⁻¹ * ∑ a : Site c,∑ b : Site c,
   (2*marble 2 P ![primary (a,(1:Axis)) u,primary (b,(1:Axis)) u])*coord a b 0^2

variable (R : Run G) (L : ∀ j, Lodge ((R.family.path.levels.clock.op j 0).patch)) (u : G.ColorIndex)

def cover (N j e : ℕ) : ℝ :=
  let V:=R.family.path.levels
  let b:=fun i=>(V.blocks i 0).branches
  let W:=Dove.model V L b R.metals.O u N (j+1)
  let T:=waken (destination V N j) (L j) W R.metals.O (b j) e 2
  ∑' x,Cork.hem T (1:Axis) 1 u u x * (x 0 : ℝ)^2

theorem cover_eq (N j e : ℕ) : coeff e (WilsonRunMarkedKineticComparison.kinetic R L u N j)=cover R L u N j e := by
  dsimp only [WilsonRunMarkedKineticComparison.kinetic,Roof.epoch,Wine.scalar,cover]
  rw [coeff_mk]
  unfold Cork.value Cork.mir Cork.net
  simp only [Pi.mul_apply,Cork.ch,pow_two]

variable {N n k r : ℕ} {S : Scene R.family.path.levels n r}
  (scene : Realized R.alloy.B.kin N n k r (Lis.sun G u) S) (j : ℕ) (lo : k≤j) (hi : j<N)

def denominator := caliper (R.family.side j n) (Lis.sun G u) (inkAt R N n j)

def old (e : ℕ) := finite (coeff e (untuned R scene j lo hi)) u

variable (V : Voice G) (paid : vacuumInvoice u V R.metals R.rolls R.alloy R.kit)

include paid in
theorem signed (e : ℕ) (positive : 0<e) :
    coeff e (WilsonConditionalTaylorSceneReset.measured R scene j lo hi)-
      coeff e (WilsonRunMarkedKineticComparison.kinetic R L u N j)=
    -(old R u scene j lo hi e+(denominator (N:=N) (n:=n) R u j)*cover R L u N j e)/
      (denominator (N:=N) (n:=n) R u j) := by
  have geo : (denominator (N:=N) (n:=n) R u j)≠0 := by
    have bound:=WilsonConditionalTaylorCaliperPayment.denominator R u V paid scene j lo hi.le
    change |denominator (N:=N) (n:=n) R u j+2|≤1 at bound
    apply ne_of_lt;linarith [(abs_le.mp bound).2]
  rw [WilsonConditionalTaylorSceneReset.measured,primitive,map_sub,coeff_one,if_neg (by omega),
    coeff_C_mul,projection,coeff_mk,cover_eq]
  rw [WilsonConditionalTaylorFiniteHessian.moment (coeff e (untuned R scene j lo hi)) u]
  change 0-(denominator (N:=N) (n:=n) R u j)⁻¹*old R u scene j lo hi e-cover R L u N j e=_
  field_simp [geo]
  ring

include paid in
theorem charge (e : ℕ) (positive : 0<e) :
    |coeff e (WilsonConditionalTaylorSceneReset.measured R scene j lo hi)-
        coeff e (WilsonRunMarkedKineticComparison.kinetic R L u N j)| ≤
      |old R u scene j lo hi e+denominator (N:=N) (n:=n) R u j*cover R L u N j e| := by
  have bound:=WilsonConditionalTaylorCaliperPayment.denominator R u V paid scene j lo hi.le
  let d:=denominator (N:=N) (n:=n) R u j
  change |d+2|≤1 at bound
  have cost : 1≤|d|:= by
    have neg : d<0:=by linarith [(abs_le.mp bound).2]
    rw [abs_of_neg neg];linarith [(abs_le.mp bound).2]
  rw [signed R L u scene j lo hi V paid e positive,abs_div,abs_neg]
  exact div_le_self (abs_nonneg _) cost

end YM.Integration.WilsonConditionalTaylorKineticIncome
end

