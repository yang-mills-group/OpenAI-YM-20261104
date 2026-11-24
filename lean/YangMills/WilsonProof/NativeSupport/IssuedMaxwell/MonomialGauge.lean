import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphGrade
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.MonomialGauge
open YM YM.Maxwell.Free YM.XSpace YM.XSpace.Normalize YM.FVA2
open YangMills.MSbar IssuedMaxwell.Reports
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup)(w:ℕ)

theorem original (rowMap:Sec g.core w→ₗ[ℂ]ℂ):
    ∃S:Finset ((B g).toCoordinates.Key→₀ℕ),∃c:((B g).toCoordinates.Key→₀ℕ)→ℂ,
      ∀v:Sec g.core w,rowMap v=∑m∈S,c m*MvPolynomial.coeff m v.val:=by
  let basis:=MS.Theater.Daylight (Press.portDeck g.core) w
  let S:Finset ((B g).toCoordinates.Key→₀ℕ):=Finset.univ.biUnion (fun i=>(basis i).val.support)
  obtain ⟨l,extension⟩:=rowMap.exists_extend
  let c (m:(B g).toCoordinates.Key→₀ℕ):=l (MvPolynomial.monomial m (1:ℂ))
  have same (v:Sec g.core w):l v.val=rowMap v:=DFunLike.congr_fun extension v
  have subset (v:Sec g.core w):v.val.support⊆S:=by
    intro m hm
    by_contra missing
    let row:Sec g.core w→ₗ[ℂ]ℂ:=(MvPolynomial.lcoeff ℂ m).comp (coeS w)
    have away (i):row (basis i)=0:=by
      change MvPolynomial.coeff m (basis i).val=0
      by_contra ne
      exact missing (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,MvPolynomial.mem_support_iff.mpr ne⟩)
    have zero:row v=0:=by
      rw [← basis.sum_repr v,map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_smul,away,smul_zero]
    exact (MvPolynomial.mem_support_iff.mp hm) zero
  refine ⟨S,c,fun v=>?_⟩
  rw [←same]
  calc
    l v.val=∑m∈v.val.support,l (MvPolynomial.monomial m (MvPolynomial.coeff m v.val)):=by
      conv_lhs=>rw [MvPolynomial.as_sum v.val]
      rw [map_sum]
    _=∑m∈v.val.support,c m*MvPolynomial.coeff m v.val:=by
      refine Finset.sum_congr rfl fun m _=>?_
      have mon:MvPolynomial.monomial m (MvPolynomial.coeff m v.val)=
          (MvPolynomial.coeff m v.val) • MvPolynomial.monomial m (1:ℂ):=by rw [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]
      rw [mon,map_smul,smul_eq_mul,mul_comm]
      rfl
    _=∑m∈S,c m*MvPolynomial.coeff m v.val:=by
      refine Finset.sum_subset (subset v) fun m _ hm=>?_
      rw [MvPolynomial.notMem_support_iff.mp hm,mul_zero]
end IssuedMaxwell.MonomialGauge
end
