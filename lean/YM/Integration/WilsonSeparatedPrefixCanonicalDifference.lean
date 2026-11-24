import YM.Integration.WilsonSeparatedPrefixCanonicalRestore
import YM.Integration.WilsonSeparatedPrefixCanonicalTapBook
import YM.MergeProof.Bungalow

/-! The actual upper and the product of its original masked singleton sections share the
same restored constant polynomial and the same original unpainted denominator. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalDifference
open Finset Function Lattice RG Wilson Extra.Histories Ac Marker Push QuadraticLocal GridApprox.Nil MergeProof MergeProof.Accent
open Extra.Multi Extra.Trajectories Lodestar WilsonSeparatedPrefixCanonicalTapBook
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V][Fintype V] (P:Rep G n)
  (φ:V → Config G n → ℂ)(h:V → Box n → Config G n → ℂ)
  (H:Support n → Config G n → Poly (Marks V))(K:Box n → Config G n → Poly (Marks V))
  (c:V → Poly (Marks V))(M:V → Support n → Config G n → Poly (Marks V))

def test (z:ℂ):Config G n → Poly (Marks (V×Bool)):=
  WilsonSeparatedPrefixCanonicalPolynomial.source P (fun Z U=>reg M U Z)
    (fun Z U=>duplicate V (H Z U)) 0 (hard h K) z

def masked (U:Config G n):Poly (Marks V):= (P.eval U:ℂ) • Poly.pass (Mach (Marks V) (fun v=>φ v U))

theorem masked_part (s:(Marks V).Mode)(U:Config G n):
    (masked P φ U).part s=(P.eval U:ℂ)*(∏v∈s.val,φ v U):=by
  rw [masked,Poly.part_smul,Mach,pass_fire]

theorem zero {a b:ℝ}(valid:P.activities.Valid P.p a b)(U:Config G n):
    restore (B:=Marks V) P φ 0 0 0 U=masked P φ U := by
  have quiet:Mach (Marks V) (fun _=>(0:ℂ))=0:=by simp [Mach]
  unfold restore masked
  simp only [Pi.zero_apply,sum_const_zero,add_zero,quiet]
  rw [show field (fun b=>bar P.activities (Marks V) U b) (flags P.p.threshold U)=
      Poly.bead (Marks V) ((P.activities.gas P.p U:ℝ):ℂ) from hawk P.activities P.p (Marks V) valid U]
  rw [mul_comm,Poly.product_bead]
  simp only [Rep.eval,Complex.ofReal_mul,mul_smul]

theorem original {a b:ℝ}(valid:P.activities.Valid P.p a b)
    (cart:∀Z U,(H Z U).part (Marks V).quiet=0)
    (cq:∀v,(c v).part (Marks V).quiet=0)(mq:∀v Z U,(M v Z U).part (Marks V).quiet=0)
    (split:∀v U,Poly.send ((Marks V).fire v) (φ v U)=c v+∑Z,M v Z U)(U:Config G n):
    let C:=duplicate V (Poly.pass (∑v,c v))
    duplicate V (restore P φ h H K U)=C*test P h H K M 1 U ∧
      duplicate V (masked P φ U)=C*test P h H K M 0 U := by
  intro C
  have full:=WilsonSeparatedPrefixCanonicalRestore.original P φ h H K c M cq mq cart split U
  have base:=WilsonSeparatedPrefixCanonicalRestore.original P φ 0 0 0 c M cq mq (by simp) split U
  constructor
  · convert full using 2
    unfold test WilsonSeparatedPrefixCanonicalPolynomial.source hard reg
    simp only [one_smul,Pi.zero_apply,zero_add,map_add,Mach,map_sum]
  · rw [←zero P φ valid U]
    convert base using 2
    unfold test WilsonSeparatedPrefixCanonicalPolynomial.source hard reg
    simp only [zero_smul,Pi.zero_apply,add_zero,map_zero]
    simp

end YM.Integration.WilsonSeparatedPrefixCanonicalDifference
end
