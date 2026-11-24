import YM.Integration.WilsonThermometerUnitFilingPinBirth
import YM.Integration.WilsonThermometerUnitFilingCoverShare
import YM.RegulatorIR.Profiles.Signal

/-! Declaring finite subsets commutes with the genuine interior translation of the issued rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinEdition
open Function Finset Gauge Lattice RG Wilson QuadraticLocal Marker QuadraticLocal.Earn Stationary
open RegulatorIR Geometry Taping Budget Budget.Packet Budget.Tuple Diagram Prim Profiles Halo Ledger Ledger.Sky Cluster
open WilsonThermometerUnitFilingCoverAudition
open scoped Classical BigOperators ENNReal

variable {G:Gauge}{n:Side}{o:Passport n Unit}{J:Census Unit}{I X:Type}
  (M:I→Row o J G X)(t:X)(a:ℂ→L[ℝ]ℝ){h:ℕ}(grade:∀ i,h ≤ (M i).lamp.toll+1)(z:Cover)

def single (i:I):Portrait G:=bank (fun _:Unit=>M i) univ t a
include grade in
theorem ink (i:I):LocalStamp (single M t a i) h:=
  WilsonThermometerUnitFilingCoverStock.original (fun _:Unit=>M i) univ _ 0 (fun _ _=>grade i)

def row (i:I):Orders (Prim.Foot G):=fun e r=>echo (carryX z) ((stamp_symbol (ink M t a grade i)).choose e r)

theorem served (i:I): BasisT h h (convey z (single M t a i)) (row M t a grade z i) ∧
    Ranks h (row M t a grade z i):=by
  have wage:=(stamp_symbol (ink M t a grade i)).choose_spec
  refine ⟨wage.1.vayne z,?_⟩
  intro e r nz
  apply wage.2 e r
  intro eq_
  apply nz
  unfold row
  rw [eq_,echo_zero]

theorem filed (s:Finset I):
    convey z (bank M s t a)=∑ i∈s,convey z (single M t a i):=by
  funext g U
  simp [convey,single,bank,WilsonThermometerUnitFilingCoverStock.portrait,Finset.sum_apply]

theorem portion (s:Finset I):BasisT h h (convey z (bank M s t a)) (∑ i∈s,row M t a grade z i) ∧
    Ranks h (∑ i∈s,row M t a grade z i):=by
  rw [filed]
  exact basis_total s (fun i=>convey z (single M t a i)) (row M t a grade z)
    (fun i _=>(served M t a grade z i).1) (fun i _=>(served M t a grade z i).2)

theorem registered {W:Type}{m:W→ℕ}{n':Page m→Side}{S:Heir n' G}{T:S.Accounts}
    (v:W)(Z:T.Report h)(s:Finset I)
    (born:BasisT h h (convey z (bank M s t a)) (Z.main (Page.opening m v))):
    Z.main (Page.opening m v)=∑ i∈s,row M t a grade z i:=by
  have all:=portion M t a grade z s
  exact certifies born all.1 (Z.ceilingM v) all.2

end YM.Integration.WilsonThermometerUnitFilingPinEdition
