import YM.Integration.WilsonCenteredRegularFiled
import YM.Integration.WilsonCenteredCrossStore
import YM.Integration.WilsonCenteredFullDensity

/-! The full ordinary two-child product minus the filed centre alternative
is a single native coefficient on the complete physical gallery. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredAbsoluteGallery
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V]
    {P : Rep G n} {o : V→Site n} {R : Census V} {d : ℕ} {F : Frame G d}

def fare (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ)
    (a b c : V) (s : R.Mode) (Z : Support n) (rad : ℕ) (E κ η μ : ℝ) : ℝ :=
  let z:=Real.exp ((p.supportExponent+2)*coverNumber p.B Z)
  let fee (r : ℝ) := cartage p Y S μ η κ r 0
  let one (I : R.Mode) := fee (stage p rad ({()}:Finset Unit)*(z*((Poly.toll w I)⁻¹*E)))
  let pair:=fee (stage p rad ({false,true}:Finset Bool)*(z*(((w a)⁻¹*E)*((w b)⁻¹*E))))
  let crossing (i j : V) := let r:=(z*((w i)⁻¹*E))*((w j)⁻¹*κ); (r+hitWidth p*η*r)/κ
  let hard (m : ℝ) := WilsonCenteredHardMount.bill p Z η m/κ
  ((((one s+one (R.fire c))+pair)+crossing a b)+crossing b a)+
    ((hard ((Poly.toll w s)⁻¹*κ)+hard ((Poly.toll w (R.fire c))⁻¹*κ))+hard (((w a)⁻¹*κ)*((w b)⁻¹*κ)))

theorem original (A : Gallery X ι o P R) (x : X) (a b c : V) (s : R.Mode)
    (apart : a≠b) (pair : s.val={a,b}) (w : V→ℝ) (hw : ∀ i,0<w i) {E κ η σ C Λ δ μ : ℝ}
    (regular : A.E.Paid w P.p.B (P.p.supportExponent+2) E)
    (hard : A.K.Paid w P.p.B P.p.supportExponent κ)
    (hk : 0<κ) (hv : 0≤η) (room : hitWidth P.p*η≤1) (width : 0≤P.p.supportExponent)
    (law : P.Lawful σ C Λ δ η) (K : Guard.Keeper P.p P.activities) (Z : Support n)
    (y : Site n) (center : y∈Z) (za : o a∈Z) (zb : o b∈Z) (zc : o c∈Z)
    (rad : ℕ) (na : separation (o a) y≤rad) (nb : separation (o b) y≤rad) (nc : separation (o c) y≤rad)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (fare P.p S Y w a b c s Z rad E κ η μ)
      (fun U=>(A.density x U).part s-(A.density x U).part (R.fire c)) := by
  have light:=WilsonCenteredRegularFiled.original A.E x a b c s pair w hw regular y Z center za zb zc rad
    na nb nc K law hk room hv S Y reader
  have left:=WilsonCenteredCrossStore.original A.E A.K x a b w hw regular hard hk hv room width law K Z y center za zb S Y
  have right:=WilsonCenteredCrossStore.original A.E A.K x b a w hw regular hard hk hv room width law K Z y center zb za S Y
  have dark:=WilsonCenteredHardFiled.original A.K w hw hard hk hv room width law K Z y center S Y x a b c s apart pair
    za zb zc (docket (ℕ×Finset ℕ)) (docket ((ℕ×ℕ)×Finset ℕ))
  obtain ⟨Q,form,paid,lit⟩:=add law hk (add law hk (add law hk light left) right) dark
  refine ⟨Q,form,paid,fun U=>?_⟩
  rw [lit]
  have α : 0≤P.p.supportExponent+2:=by linarith
  exact (WilsonCenteredFullDensity.original A a b c s apart pair x U (regular.sums α hw x U)
    (Hard.packet_summing _ hard width hw x U)).symm

end YM.Integration.WilsonCenteredAbsoluteGallery
