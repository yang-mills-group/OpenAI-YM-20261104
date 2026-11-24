import YM.Integration.WilsonMarkedIndependentMixedMomentTensor

/-! The complete formal moment at the same finite Wilson period. All products
use disjoint portions of the same squarefree marked input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedMomentProduct
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open WilsonMarkedIndependentMixedMomentTensor (Tensor)
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D:ι→ℕ}{m e:ℕ}{n:ℕ→Side}{t:ℕ→ℝ}{S J:Finset ι}

theorem product (sub:J⊆S)(ht:∀p,0≤t p)
    (X:ℕ→Era G (Pen D J))(Y:ℕ→Era G (Pen D (S\J)))
    (left:Tensor G (Pen D J) m e n t X)(right:Tensor G (Pen D (S\J)) m e n t Y):
    Tensor G (Pen D S) m e n t (fun N=>waxV sub (X N) (Y N)):=by
  intro i hi r x
  simp only [waxV,foam,Finset.sum_apply]
  apply WilsonMarkedIndependentMixedMomentPrice.summed ht
  intro a ha
  have deg:a.1+a.2=i:=by simpa using ha
  simp only [cob,swirl,Pi.smul_apply,Finset.sum_apply]
  apply WilsonMarkedIndependentMixedMomentPrice.smul
  apply WilsonMarkedIndependentMixedMomentPrice.summed ht
  intro π _
  apply WilsonMarkedIndependentMixedMomentPrice.summed ht
  intro b hb
  have hit:b.1+b.2=r:=by simpa using hb
  simp only [cobT,dif_pos hit]
  exact WilsonMarkedIndependentMixedMomentPrice.joined (joinL sub D)
    (left a.1 (by omega) _ ((x ∘ π) ∘ Fin.cast hit ∘ Fin.castAdd b.2))
    (right a.2 (by omega) _ ((x ∘ π) ∘ Fin.cast hit ∘ Fin.natAdd b.1))

theorem moment (Y:ℕ→family G D)(ht:∀p,0≤t p)(S:Finset ι)
    (read:∀J⊆S,Tensor G (Pen D J) m e n t (fun N=>Y N J)):
    Tensor G (Pen D S) m e n t (fun N=>levelsO (Y N) S):=by
  induction S using Finset.strongInductionOn
  case _ S ih=>
    by_cases blank:S=∅
    · subst S;simpa only [empty_level] using WilsonMarkedIndependentMixedMomentTensor.puffed (G:=G) (m:=m) (e:=e) (n:=n) D ht
    rw [show (fun N=>levelsO (Y N) S)=(fun N=>(S.card:ℝ)⁻¹ • ∑J∈S.powerset,if w:J⊆S ∧ J≠∅ then
      (J.card:ℝ) • waxV w.1 (Y N J) (levelsO (Y N) (S\J)) else 0) by
        funext N;rw [levelsO,dif_neg blank]]
    apply WilsonMarkedIndependentMixedMomentTensor.smul
    apply WilsonMarkedIndependentMixedMomentTensor.sum _ _ ht
    intro J _
    by_cases member:J⊆S ∧ J≠∅
    · simp only [dif_pos member]
      apply WilsonMarkedIndependentMixedMomentTensor.smul
      exact product member.1 ht _ _ (read J member.1) (ih _ (sh_k member.1 member.2) fun T touch=>read T (touch.trans sdiff_subset))
    · simp only [dif_neg member]
      exact WilsonMarkedIndependentMixedMomentTensor.zero ht

end YM.Integration.WilsonMarkedIndependentMixedMomentProduct
end
