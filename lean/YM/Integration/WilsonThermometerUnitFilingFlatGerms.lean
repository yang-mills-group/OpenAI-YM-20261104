import YM.Integration.WilsonThermometerUnitFilingShortAssay

/-! At the actual flat endpoint, only rank-zero marked words survive, at their true coupling grades. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatGerms
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Exterior Stationary Comparison.RG02 AllOrder AllOrder.Floe AllOrder.Floe.Step
open PertExtension.Series PertExtension.Series.Radial
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V α:Type} [DecidableEq V] {P:Passport n V} {J:Census V} (T:Row P J G α)

theorem empty_color (slot:Slot) (y:Site n):slot.atSite (1:Config G n) y=0:=by
  rw [Work.F03.atSite_path]
  simp [faceValue,square,G.curvature_unit]

theorem positive_rank (hr:0<T.lamp.r) : T.atom.unmasked (1:Config G n) T.center=0:=by
  unfold Atom.unmasked Atom.poly
  refine sum_eq_zero fun b _=>mul_eq_zero_of_right _ ?_
  exact prod_eq_zero (mem_univ (⟨0,hr⟩:Fin T.lamp.r))
    (by change ((T.atom.leg ⟨0,hr⟩).atSite (1:Config G n) T.center) (b ⟨0,hr⟩)=0;rw [empty_color];rfl)

theorem filed_grade (k:ℕ) : T.markReceipt k (0:Link G n)=
    if T.lamp.r=0 ∧ k=T.lamp.e then T.atom.unmasked (1:Config G n) T.center else 0:=by
  have vanish (d:ℕ) (hd:d≠0):
      Radial.jet (Helmet.frame T.atom T.center) d (0:Link G n)=0:=by
    have he:=Tensor.homogeneous (Tensor.coeff (Helmet.frame T.atom T.center) d 0) (0:Link G n) (0:ℝ)
    rw [zero_smul,zero_pow hd,zero_smul] at he
    exact he
  unfold Row.markReceipt
  by_cases take:T.lamp.e≤k
  · rw [if_pos take]
    by_cases exactGrade:T.lamp.r=0 ∧ k=T.lamp.e
    · rw [if_pos exactGrade,show k-T.lamp.e+T.lamp.r=0 by omega]
      change Assembly.jet (Helmet.frame T.atom T.center) 0 (0:Link G n)=_
      rw [Assembly.jet_zero,Helmet.frame,input_zero]
    · have neq:k-T.lamp.e+T.lamp.r≠0:=by intro bad;apply exactGrade;constructor <;> omega
      rw [if_neg exactGrade,vanish _ neq]
  · rw [if_neg take,if_neg (show ¬(T.lamp.r=0 ∧ k=T.lamp.e) from fun h=>take h.2.ge)]

theorem realization (g:ℝ) (x:α) {p:ℕ} (hp:T.lamp.e≤p):
    T.nominal g x (1:Config G n)=∑j∈range (p+1),(g:ℂ)^j*(T.paint x*(T.markReceipt j (0:Link G n):ℂ)):=by
  classical
  by_cases zeroRank:T.lamp.r=0
  · rw [sum_eq_single_of_mem T.lamp.e (mem_range.mpr (by omega))]
    · rw [filed_grade,if_pos ⟨zeroRank,rfl⟩]
      simp only [Row.nominal,Pi.smul_apply,smul_eq_mul,Row.grain,Loan.lag,zeroRank,
        Nat.cast_zero,sub_zero,zpow_natCast,Complex.ofReal_mul,Complex.ofReal_pow]
      ring
    · intro j _ ne
      rw [filed_grade,if_neg (fun h=>ne h.2)]
      simp
  · have disappear:=positive_rank T (Nat.pos_of_ne_zero zeroRank)
    simp [filed_grade,zeroRank,Row.nominal,Row.grain,disappear]

end YM.Integration.WilsonThermometerUnitFilingFlatGerms
