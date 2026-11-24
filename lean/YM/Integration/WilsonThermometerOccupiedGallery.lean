import YM.Integration.WilsonThermometerOccupiedHard
import YM.Integration.WilsonThermometerOccupiedInterpolation

/-! Four real reweightings of every occupied K at the original eligible addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOccupiedGallery
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push Push.Corrected Push.AbsoluteSums
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached RG3.Letters MeasureTheory
open WilsonThermometerOccupiedHard WilsonThermometerOccupiedPolynomial WilsonThermometerOccupiedInterpolation
open scoped Classical BigOperators
variable {R : Census (Fin 3)} {G:Gauge} {n:Side} {P:Rep G n} {o:Fin 3→Site n} {X ι:Type*}

def gallery (z:ℂ) (A:Gallery X ι o P R) : Gallery X ι o P R := ⟨A.E, hard z A.K⟩

theorem decomposition (p:Poly R) (z:ℂ):
    paint z p=paint 0 p+Poly.bead R z*(p-paint 0 p):=by
  rw [Poly.product_bead]
  ext1 s
  change amount z s*p.part s=amount 0 s*p.part s+z*(p.part s-amount 0 s*p.part s)
  by_cases h:s=R.quiet <;> simp [amount,h]

theorem kept (p:Poly R):Order 1 (p-paint 0 p):=by
  intro s hs
  have eq:s=R.quiet:=Subtype.ext (Finset.card_eq_zero.mp (by omega))
  change p.part s-amount 0 s*p.part s=0
  simp [amount,eq]

theorem packet (A:Gallery X ι o P R) (x:X) (U:Config G n) (l:Finset ℕ)
    (q T:ℝ) (inv:q*T=1):
    Attached.packet P.activities P.p (A.K.hard x) U l =
      fitted q (Attached.packet P.activities P.p ((gallery 0 A).K.hard x) U l)
        (Attached.packet P.activities P.p ((gallery T A).K.hard x) U l)
        (Attached.packet P.activities P.p ((gallery (2*T) A).K.hard x) U l)
        (Attached.packet P.activities P.p ((gallery (3*T) A).K.hard x) U l) := by
  by_cases eligible:P.activities.admissible P.p U l
  · simp only [Attached.packet,if_pos eligible]
    let a:=fun i=>paint 0 (A.K.hard x i U)
    let d:=fun i=>A.K.hard x i U-a i
    obtain ⟨C⟩:=WilsonThermometerOccupiedPolynomial.product a d (fun i=>kept (A.K.hard x i U)) l
    have atNode (z:ℂ):(∏i∈l,(a i+Poly.bead R z*d i))=∏i∈l,(gallery z A).K.hard x i U := by
      apply Finset.prod_congr rfl
      intro i _
      exact (decomposition (A.K.hard x i U) z).symm
    have values:=readings C q T inv
    simp_rw [atNode] at values
    simpa only [gallery,identity] using values
  · simp only [Attached.packet,if_neg eligible,fitted,sub_self,smul_zero,add_zero]

theorem field (A:Gallery X ι o P R) (x:X) (U:Config G n) (w:Fin 3→ℝ) (wp:∀v,0<w v)
    (q T B:ℝ) (inv:q*T=1)
    (fund:∀z∈({0,(T:ℂ),2*(T:ℂ),3*(T:ℂ)}:Finset ℂ),(gallery z A).K.Paid w P.p.B P.p.supportExponent B):
    A.density x U =
      fitted q ((gallery 0 A).density x U) ((gallery T A).density x U)
        ((gallery (2*T) A).density x U) ((gallery (3*T) A).density x U) := by
  have sums (z) (hz:z∈({0,(T:ℂ),2*(T:ℂ),3*(T:ℂ)}:Finset ℂ)) :=
    Hard.packet_summing _ (fund z hz) P.p.exponent_pos.le wp x U
  have all:=summed q _ _ _ _ (sums 0 (by simp)) (sums T (by simp))
    (sums (2*(T:ℂ)) (by simp)) (sums (3*(T:ℂ)) (by simp))
  have gas:A.gas x U=fitted q ((gallery 0 A).gas x U) ((gallery T A).gas x U)
        ((gallery (2*T) A).gas x U) ((gallery (3*T) A).gas x U):=by
    change (∑'l,Attached.packet P.activities P.p (A.K.hard x) U l)=_
    simp_rw [packet A x U _ q T inv]
    exact all
  simp only [Gallery.density,gas,gallery,fitted,mul_add,mul_smul_comm,mul_sub,smul_add,smul_sub,
    smul_comm (Complex.ofReal (Real.exp (P.exponent U)))]

theorem origin (A:Gallery X ι o P R) (x:X) (U:Config G n) (w:Fin 3→ℝ) (wp:∀v,0<w v)
    {B:ℝ} (fund:(gallery 0 A).K.Paid w P.p.B P.p.supportExponent B):
    (gallery 0 A).density x U=(P.eval U:ℂ) • Poly.pass (A.E.log x U) :=by
  let H:=(gallery 0 A).K
  have row (i):H.hard x i U=Poly.bead R (P.activities.K i U:ℂ):=by
    ext1 s
    rw [show (H.hard x i U).part s=if s=R.quiet then (P.activities.K i U:ℂ) else 0
      from WilsonThermometerOccupiedHard.origin A.K x i U s]
    simp [Poly.bead,Poly.part_send]
  have cover (l:Finset ℕ): (∏ i∈l,H.hard x i U)=Poly.bead R (∏i∈l,(P.activities.K i U:ℂ)):=by
    calc
      _ = ∏i∈l,Poly.bead R (P.activities.K i U:ℂ):=
        Finset.prod_congr rfl fun i _=>row i
      _ = _ := (map_prod (Poly.bead R) (fun i=>(P.activities.K i U:ℂ)) l).symm
  have sm:=Hard.packet_summing _ fund P.p.exponent_pos.le wp x U
  have base:(gallery 0 A).gas x U=Poly.bead R (P.activities.gas P.p U:ℂ):=by
    ext1 s
    by_cases eq:s=R.quiet
    · subst s
      exact (Hard.packet_of_quiet _ x U sm).trans (by simp [Poly.bead,Poly.part_send])
    · rw [show ((gallery 0 A).gas x U).part s=∑'l,(Attached.packet P.activities P.p (H.hard x) U l).part s
        from Poly.share sm s]
      have off (l): (Attached.packet P.activities P.p (H.hard x) U l).part s=0:=by
        unfold Attached.packet
        split
        · rw [cover]; change (Poly.send R.quiet _).part s=0; rw [Poly.part_send,if_neg eq]
        · rfl
      simp [off,Poly.bead,Poly.part_send,eq]
  rw [Gallery.density,base,mul_comm,Poly.product_bead,smul_smul]
  rw [Rep.eval,Complex.ofReal_mul]
  rfl

end YM.Integration.WilsonThermometerOccupiedGallery
