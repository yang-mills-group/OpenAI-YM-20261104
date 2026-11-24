import YM.Integration.WilsonPhysicalCentralPolynomial
import YM.WilsonCoeffUV.FieldRead.Engineering

/-! Central inversion on the honest field and each individual test-address leg. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalCentralAddress
open Labels WilsonPhysicalCentralPolynomial WilsonPhysicalCentralInversion
open WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open scoped BigOperators Classical
variable {G:Gauge}{h:ℕ}

theorem homogeneous (d:ℕ×ℕ) {p:Label G h} (pure:p∈Grade d):
    tensor flip p=(-1:ℂ)^d.1 • p:=by
  apply Subtype.ext
  ext m
  change MvPolynomial.coeff m (rotated flip p.val)=MvPolynomial.coeff m (((-1:ℂ)^d.1) • p.val)
  rw [coefficient,MvPolynomial.coeff_smul,smul_eq_mul]
  by_cases yes:MvPolynomial.coeff m p.val=0
  · simp [yes]
  · have hd:=(pure_grade d p).mp pure yes
    rw [weight_slot] at hd
    rw [show height m=d.1 from congrArg Prod.fst hd]

theorem field (F:Frame G h) (i j:F.Index):
    bleached F flip i j=if i=j then (-1:ℝ)^(F.grades j).1 else 0:=by
  have act:F.act flip (Pi.single j 1)=(-1:ℂ)^(F.grades j).1 • Pi.single j 1:=calc
    _=F.act flip (F.coords (F.basis j)):=by rw [F.coords_basis]
    _=_:=by rw [F.act_coords,homogeneous _ (F.pure j),map_smul,F.coords_basis]
  rw [bleached,act]
  split_ifs with e
  · subst i
    simp
    norm_cast
  · simp [Pi.single_eq_of_ne e]

theorem address (m:Multiset Axis):hue inversion m=(-1:ℝ)^m.card:=by
  induction m using Multiset.induction_on with
  | empty=>simp [hue]
  | cons a t ih=>
    change (Multiset.map _ (a::ₘt)).prod=_
    rw [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons,pow_succ]
    change (-1:ℝ)*hue inversion t=_
    rw [ih,mul_comm]

theorem same_address (w:Spiral h):spindle inversion w=w:=by
  apply Subtype.ext
  simp [spindle,inversion]

theorem whole (F:Frame G h) (i j:Alma F):
    blueIn F inversion i j=if i=j then (-1:ℝ)^(weight F j) else 0:=by
  rw [blueIn,same_address,address,field]
  by_cases same:i=j
  · subst i
    simp [weight,weave,rankS,pow_add,mul_comm]
  · by_cases slot:notar F j=notar F i
    · have diff:sheet F i≠sheet F j:=by
        intro eq
        exact same (Subtype.ext (Prod.ext eq slot.symm))
      simp [slot,diff,same]
    · simp [slot,same]

end YM.Integration.WilsonPhysicalCentralAddress
