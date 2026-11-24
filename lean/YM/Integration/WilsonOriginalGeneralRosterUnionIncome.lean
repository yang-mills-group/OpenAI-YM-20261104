import YM.Integration.WilsonOriginalGeneralRosterFiledIncome
import YM.Integration.WilsonOriginalGeneralRosterUnionPhysical

/-! The whole finite collection of trials chooses its fractional losses before
the fiscal order. Every physical branch in the common field market crosses the
required gate, including when the same stock is used in more than one row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterUnionIncome
open Function Set Filter Finset Lattice RG Wilson Source Labels Climb Trace.Pilot
open Spec Table Extraction PhysMS WilsonLimitConstruction GapsContact GapsContact.Ascent PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalGeneralRosterUnion (Row)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonReflectedPublicStationFare (station)
open WilsonOriginalGeneralRosterFiledIncome (Purchased)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][Nonempty I]{D T:ℕ}{δ:ℝ}

theorem original {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}{simple:G.Simple}
    {campaign:Campaign R}{W:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign W)(bliss:Bliss F l z H)
    (h:ℕ)(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(d:I→Fin (D+1))
    {B:Type}[Fintype B](rows:B→Row I)(γ:ℝ)(gp:0<γ):
    ∃η:(w:B)→Fin (rows w).size→ℝ,(∀w i,0<η w i) ∧ (∑w,∑i,η w i)<γ ∧
    ∃L:ℕ,(∀w,Purchased R (fun i=>(d ((rows w).stock i)).val) (η w) L) ∧
    ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      ∀ i b, L ≤ station F ((books (ρ i)).rows (d i)) b:=by
  classical
  let allot:=γ/((Fintype.card B:ℝ)+1)
  have allotPos:0<allot:=div_pos gp (by positivity)
  have wide (j:ℕ):1≤(R.family.path.levels.budget j).supportExponent:=by rw [paid.support];norm_num
  have grants:=WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid
  choose η each bound L funded using fun w:B=>WilsonOriginalGeneralRosterFiledIncome.original R
    (fun i=>(d ((rows w).stock i)).val) simple grants.1 wide allot allotPos
  have expenses:(∑w,∑i,η w i)<γ:=by
    calc
      _≤∑_w:B,allot:=sum_le_sum fun w _=>(bound w).le
      _<γ:=by
        simp only [allot,sum_const,card_univ,nsmul_eq_mul]
        rw [←mul_div_assoc,div_lt_iff₀ (by positivity:0<(Fintype.card B:ℝ)+1)]
        nlinarith only [gp]
  let gate:=univ.sup L
  refine ⟨η,each,expenses,gate,?_,?_⟩
  · intro w N per f K fk cut req power t amount A file stations axes reached deep
    exact funded w N per f K fk cut req power t amount A file stations axes
      (fun i=>(le_sup (f:=L) (mem_univ w)).trans (reached i)) deep
  · filter_upwards [WilsonAddressedMixedStationRange.original F simple bliss grants.2.1 D T h gate d books] with r late
    exact fun ρ span near i b=>((late ρ span near).2 i b).1

end YM.Integration.WilsonOriginalGeneralRosterUnionIncome
end
