import YM.Integration.WilsonOlderFreshSoftSocketStationSettlement
import YM.Integration.WilsonOriginalTwoFlatRoseFiledVisit

/-! The original nonzero dose is divided out once on its charged physical cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationDose
open RG PhysicalNext.Repeat.Legato Finset
open WilsonPositionThermometerConnected (value)
open WilsonOriginalTwoFlatRoseMerFigure (restoration)
open WilsonOriginalTwoFlatIRFlatMarked (seat)
open WilsonOlderFreshSoftSocketStationSettlement (Book put)
open scoped Classical BigOperators

abbrev Mask:=Finset (Fin 3)
def stamp (c:Fin 3→ℂ)(s:Mask):ℂ:=∏a∈s,c a

theorem homogeneous (c:Fin 3→ℂ)(F:Mask→ℂ):value (fun s=>stamp c s*F s)=stamp c univ*value F:=by
  simp [value,stamp,Fin.prod_univ_three]
  ring

theorem occupied {F Q:Mask→ℂ}(h:∀s:Mask,s.Nonempty→F s=Q s):value F=value Q:=by
  unfold value
  rw [h univ ⟨0,mem_univ _⟩,h {0,1} ⟨0,by decide⟩,h {2} ⟨2,by decide⟩,
    h {0,2} ⟨0,by decide⟩,h {1} ⟨1,by decide⟩,h {1,2} ⟨1,by decide⟩,h {0} ⟨0,by decide⟩]

variable {G:Gauge}(R:Run G)
def outside (r:ℝ)(d:Fin 3→ℕ)(cash:Fin 3→ℂ)(i:Fin 3):ℂ:=(r:ℂ)^(d i)/cash i

theorem compensated (f n:ℕ)(r:ℝ)(d:Fin 3→ℕ)(cash:Fin 3→ℂ)(funded:∀i,cash i ≠ 0)(s:Mask):
    stamp (outside r d cash) s*
      restoration R (f:=f) (n:=n) (grades:=d) (fun _=>WilsonReceivedChronologicalSocket.lit (V:=Fin 3)) cash (seat s)=
      ∏a∈s,(((r/R.family.S.a (f+n))^(d a):ℝ):ℂ):=by
  unfold stamp outside restoration WilsonOriginalMicroscopicEntranceDoseGrid.mass WilsonOriginalMicroscopicEntranceFiling.units
    WilsonOriginalTwoFlatRoseMerRestored.marked
  simp only [WilsonReceivedChronologicalSocket.lit,seat,Finset.prod_const_one,mul_one]
  rw [←mul_assoc,←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [div_mul_cancel₀ _ (funded i)]
  push_cast
  rw [div_pow,div_eq_mul_inv]

theorem scaled (f n:ℕ)(r:ℝ)(d:Fin 3→ℕ)(cash:Fin 3→ℂ)(funded:∀i,cash i ≠ 0)(s:Mask)(z:ℂ):
    stamp (outside r d cash) s*
      (restoration R (f:=f) (n:=n) (grades:=d) (fun _=>WilsonReceivedChronologicalSocket.lit (V:=Fin 3)) cash (seat s)*z)=
      WilsonOlderFreshSoftRoseMarket.scaled s (fun i=>(r/R.family.S.a (f+n))^(d i)) z:=by
  rw [←mul_assoc,compensated R f n r d cash funded]
  apply congrArg (fun x:ℂ=>x*z)
  simp only [WilsonOlderFreshSoftRoseCourse.seat,Complex.ofReal_prod]
  exact (Finset.prod_coe_sort s (fun i=>(((r/R.family.S.a (f+n))^(d i):ℝ):ℂ))).symm

end YM.Integration.WilsonOlderFreshSoftSocketStationDose
end
