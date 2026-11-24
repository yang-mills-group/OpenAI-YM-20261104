import YM.Integration.WilsonReceivedDepositedOrbitalEquation

/-! The original ring-valued marker equations survive registering the measured
coupling, multiplying the elected per-source salaries, and retaining any
specified subfamily of actual sheets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalGrade
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Blue PowerSeries
open WilsonReceivedDepositedOrbitalMode (face letters)
open WilsonReceivedDepositedOrbitalColumns (row)
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
open WilsonOriginalMixedGaussianTable (stock)
open WilsonVacuumPreResetFiniteRegister (register)
open scoped Classical BigOperators
variable {V H U:Type}[Fintype V][DecidableEq V]
local notation "J" => Stock.census V

def booked (r:ℕ)(B:U→ℝ)(w:V→ℂ)(M:Finset V→Ink U):Grade (J) r:=
  stock (J) r B (fun s:Finset V=>∏j∈s,coefficient (J) (J).fire w j) M

def thermal (V:Type)[Fintype V][DecidableEq V](r:ℕ)(B:U→ℝ):Ink U→+*Poly (indices r):=
  ((Join.projectRight (Stock.census V) (indices r)).toRingHom.comp (register (Stock.census V) r)).comp
    (PowerSeries.map (MvPolynomial.eval B))

theorem at_row (r:ℕ)(B:U→ℝ)(w:V→ℂ)(M:Finset V→Ink U)(s:Finset V):
    row (booked r B w M) s=(∏i∈s,w i) • thermal V r B (M s):=by
  apply Marker.Poly.ext
  intro t
  change (stock _ _ _ _ _).part (Join.pair (face s) t)=_
  rw [WilsonOriginalMixedGaussianTable.value,Poly.part_smul]
  simp_rw [letters,Poly.part_send]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl]
    change _=(∏i∈s,w i)*(register (J) r (PowerSeries.map (MvPolynomial.eval B) (M s))).part
      (Join.pair (J).quiet t)
    rw [WilsonVacuumPreResetFiniteRegister.read,if_pos rfl,coeff_map,mul_assoc]
  · intro b _ ne
    have distinct:face s≠face b:=fun e=>ne (congrArg Subtype.val e).symm
    rw [if_neg distinct,zero_mul,zero_mul]
  · simp

section
variable {α β A:Type}[DecidableEq α][DecidableEq β][CommRing A]
theorem restrict (f:α↪β){M L:Sac β A}(law:Equation M L):
    Equation (fun s=>M (s.map f)) (fun s=>L (s.map f)):=by
  refine ⟨by simpa using law.1,by simpa using law.2.1,?_⟩
  funext s
  have wage:=congrFun law.2.2 (s.map f)
  change (s.map f).card • M (s.map f)=∑u∈(s.map f).powerset,
    (u.card • L u)*M (s.map f\u) at wage
  have parts:(s.map f).powerset=s.powerset.image (fun t=>t.map f):=by
    simp only [Finset.map_eq_image,Finset.powerset_image]
  rw [parts,Finset.sum_image] at wage
  · simpa only [dial,shells,Finset.card_map,←Finset.map_sdiff] using wage
  · intro a _ b _ eq
    exact Finset.map_injective f eq
end

section
variable {α A:Type}[DecidableEq α][CommRing A][Algebra ℂ A]
theorem earnings (w:α→ℂ){M L:Sac α A}(law:Equation M L):
    Equation (fun s=>(∏i∈s,w i) • M s) (fun s=>(∏i∈s,w i) • L s):=by
  refine ⟨by simp [law.1],by simp [law.2.1],?_⟩
  funext s
  have wage:=congrFun law.2.2 s
  change s.card • M s=∑u∈s.powerset,(u.card • L u)*M (s\u) at wage
  change s.card • ((∏i∈s,w i) • M s)=∑u∈s.powerset,
    (u.card • ((∏i∈u,w i) • L u))*((∏i∈s\u,w i) • M (s\u))
  rw [smul_comm,wage,Finset.smul_sum]
  refine Finset.sum_congr rfl fun u hu=>?_
  rw [smul_comm u.card,smul_mul_smul_comm,mul_comm (∏i∈u,w i),Finset.prod_sdiff (mem_powerset.mp hu)]
end

theorem logged (r:ℕ)(B:U→ℝ)(w:V→ℂ){M L:Finset V→Ink U}(law:Equation M L):
    Extra.Trajectories.connected (booked r B w M)=booked r B w L:=by
  have h:=earnings w (law.mapKin (thermal V r B))
  change Equation (fun s=>(∏i∈s,w i) • thermal V r B (M s))
    (fun s=>(∏i∈s,w i) • thermal V r B (L s)) at h
  simp_rw [←at_row] at h
  letI : IsAddTorsionFree (Poly (indices r)):=.of_isTorsionFree ℂ (Poly (indices r))
  apply WilsonReceivedDepositedOrbitalColumns.ext
  exact Equation.unique _ _ _ (WilsonReceivedDepositedOrbitalEquation.original _ h.1) h

end YM.Integration.WilsonReceivedDepositedOrbitalGrade
end
