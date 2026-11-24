import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCorrelation
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphGrade
open YM YM.Maxwell.Free YM.XSpace YM.XSpace.Normalize YM.FVA2 YM.FVA2.O.Score
open YangMills.MSbar IssuedMaxwell.Reports
variable (g:YangMills.GaugeGroup){d:ℕ}
theorem original (a:Sec g.core d):
    Ordinary.homogeneous (B g) d a.val ↔ at_grade a:=by
  constructor
  · intro hom
    apply Subtype.ext
    change engineering d g.core a.val=a.val
    ext m
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    split_ifs with h
    · rfl
    · by_contra hn
      exact h (hom m (MvPolynomial.mem_support_iff.mpr (Ne.symm hn)))
  · intro top m hm
    rw [←top] at hm
    exact (part d d a).property.2 (MvPolynomial.mem_support_iff.mp hm)
end IssuedMaxwell.GraphGrade
end
