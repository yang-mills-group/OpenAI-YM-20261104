import YM.Integration.WilsonCenteredSingletonMass
import YM.Integration.WilsonCenteredAbsoluteGallery

/-! A signed physical singleton with independent raw force price and outgoing
forced divisor. The complete compatible hard gas is assembled before division. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOlderSignedSingletonFare
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories Extra.Histories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V]
    {P : Rep G n} {o : V→Site n} {R : Census V} {d : ℕ} {F : Frame G d}

def fare (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ)
    (s : R.Mode) (z : ℂ) (Z : Support n) (rad : ℕ) (E Kraw κ η μ : ℝ) :=
  cartage p Y S μ η κ
    ((‖z‖*stage p rad ({()}:Finset Unit))*(Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*((Poly.toll w s)⁻¹*E)))
    ((‖z‖*WilsonCenteredHardMount.bill p Z η ((Poly.toll w s)⁻¹*Kraw))/κ)

theorem original (A : Gallery X ι o P R) (x : X) (c : V) (z : ℂ) (w : V→ℝ) (hw : ∀ i,0<w i)
    {E Kraw κ η σ C Λ δ μ : ℝ} (regular : A.E.Paid w P.p.B (P.p.supportExponent+2) E)
    (hard : A.K.Paid w P.p.B P.p.supportExponent Kraw)
    (hk : 0<κ) (hv : 0≤η) (room : hitWidth P.p*η≤1) (width : 0≤P.p.supportExponent)
    (law : P.Lawful σ C Λ δ η) (K : Guard.Keeper P.p P.activities) (Z : Support n)
    (y : Site n) (center : y∈Z) (seat : o c∈Z) (rad : ℕ) (near : separation (o c) y≤rad)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (fare P.p S Y w (R.fire c) z Z rad E Kraw κ η μ)
      (fun U=>z*(A.density x U).part (R.fire c)) := by
  let serial:=docket (ℕ×Finset ℕ)
  let f:=WilsonCenteredHardMount.first A.K K Z (R.fire c) x serial
  have width' : 0≤P.p.supportExponent+2 := by linarith
  obtain ⟨I,count,paid,literal⟩:=WilsonCenteredPaidPublisher.original A.E w hw width' regular
  letI : Countable I:=count.to_subtype
  let L:=WilsonCenteredPaidPublisher.keep A.E I
  have cash : L.Paid w P.p.B (P.p.supportExponent+2) E:=paid
  have account:=WilsonCenteredHardMount.single A.K w hw hard law.labels.boundK hv room K law.labels.forced
    Z y center (R.fire c) c (mem_singleton_self _) seat x serial
  obtain ⟨fit,bill⟩:=WilsonCenteredSingletonMass.scaled z f account.1 account.2
  obtain ⟨Q,format,amount,eqn⟩:=single L x (R.fire c) c (mem_singleton_self _) w hw cash y Z center seat rad near z
    K law hk room hv S Y reader (z•f) fit (by
      rw [mul_div_cancel₀ _ hk.ne']
      exact bill)
  refine ⟨Q,format,amount,fun U=>?_⟩
  have born:=Hard.packet_summing A.K hard width hw x U
  have mark:=WilsonCenteredSingletonMass.first A.K K Z x U c serial account.2 law.labels.boundK born
  rw [eqn]; dsimp only
  rw [show L.log x U=A.E.log x U from literal x U]
  have scaledRead : (∑' B, gasMark P.p P.activities U B (z•f))=z*WilsonCenteredHardAnswers.read (P:=P) f U := by
    simp [WilsonCenteredHardAnswers.read,map_smul,tsum_mul_left,smul_eq_mul]
  rw [scaledRead,mark,WilsonCenteredSingletonMass.ordinary A x U c (regular.sums width' hw x U) born]
  change _=z*((P.eval U:ℂ)*(A.E.log x U).part (R.fire c)+(Real.exp (P.exponent U):ℂ)*(WilsonCenteredAbsoluteHard.gas A.K x U).part (R.fire c))
  ring

end YM.Integration.WilsonOlderSignedSingletonFare
