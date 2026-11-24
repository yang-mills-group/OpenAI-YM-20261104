import YM.Integration.WilsonCenteredFiledAtoms
import YM.Integration.WilsonCenteredPaidPublisher

/-! The regular mixed moment and the filed alternative are placed at the
same physical root. Each child retains its declared address. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredRegularFiled
open Finset Function Lattice RG Wilson Marker Ac QuadraticLocal Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms Comparison.RG02.Cumulants
open WilsonCenteredLampCapture WilsonCenteredMountedCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V]
    {P : Rep G n} {o : V→Site n} {R : Census V} {d : ℕ} {F : Frame G d}

private theorem blank (y : Site n) : ForceFormat P.p P.activities y 0 :=
  ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩

omit [Fintype V] in
theorem original (L : Lamps X ι G P.p o R) (x : X) (a b c : V) (s : R.Mode) (pair : s.val={a,b})
    (w : V→ℝ) (hw : ∀ i,0<w i) {E : ℝ} (regular : L.Paid w P.p.B (P.p.supportExponent+2) E)
    (y : Site n) (Z : Support n) (root : y∈Z) (za : o a∈Z) (zb : o b∈Z) (zc : o c∈Z) (rad : ℕ)
    (na : separation (o a) y≤rad) (nb : separation (o b) y≤rad) (nc : separation (o c) y≤rad)
    (K : Guard.Keeper P.p P.activities) {σ C Λ δ η κ μ : ℝ}
    (law : P.Lawful σ C Λ δ η) (div : 0<κ) (room : hitWidth P.p*η≤1) (hη : 0≤η)
    (S : SectionData F) (Y : Hol G) (read : Readable Y S P.p n μ) :
    let Zfee := Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)
    let t₁:=stage P.p rad ({()}:Finset Unit)
    let t₂:=stage P.p rad ({false,true}:Finset Bool)
    let fee (r : ℝ) := cartage P.p Y S μ η κ r 0
    Store P S Y y κ
      ((fee (t₁*(Zfee*((Poly.toll w s)⁻¹*E)))+fee (t₁*(Zfee*((Poly.toll w (R.fire c))⁻¹*E))))+
        fee (t₂*(Zfee*(((w a)⁻¹*E)*((w b)⁻¹*E)))))
      (fun U=>(P.eval U:ℂ)*(L.log x U).part s-(P.eval U:ℂ)*(L.log x U).part (R.fire c)+
        (P.eval U:ℂ)*((L.log x U).part (R.fire a)*(L.log x U).part (R.fire b))) := by
  intro Zfee t₁ t₂ fee
  have width : 0≤P.p.supportExponent+2 := by have:=P.p.exponent_pos;linarith
  obtain ⟨A,count,paid,exactAt⟩ := WilsonCenteredPaidPublisher.original L w hw width regular
  letI : Countable A:=count.to_subtype
  let D:=WilsonCenteredPaidPublisher.keep L A
  have use : D.Paid w P.p.B (P.p.supportExponent+2) E:=paid
  have no : ForceCost P.p P.activities (0 : ℕ → Config G n→ℂ) (κ*0) := by
    rw [mul_zero];exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  have mixed := single D x s a (by rw [pair];simp) w hw use y Z root za rad na 1 K law div room hη S Y read 0 (blank _) no
  have centre := single D x (R.fire c) c (mem_singleton_self _) w hw use y Z root zc rad nc 1 K law div room hη S Y read 0 (blank _) no
  have product := couple D D x a b w hw use use y Z root za zb rad na nb 1 K law div room hη S Y read 0 (blank _) no
  obtain ⟨Q,form,bill,literal⟩:=add law div (sub law mixed centre) product
  refine ⟨Q,form,?_,fun U=>?_⟩
  · simpa only [norm_one,one_mul] using bill
  rw [literal]
  simp only [Pi.add_apply,Pi.sub_apply,map_zero,tsum_zero,mul_zero,add_zero,one_mul]
  rw [show D.log x U=L.log x U from exactAt x U]

end YM.Integration.WilsonCenteredRegularFiled
