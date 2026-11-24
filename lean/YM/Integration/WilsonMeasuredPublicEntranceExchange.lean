import YM.Integration.WilsonMeasuredPublicEntranceOrder

/-! Full upper entrance at one lower held field, with all previously received mixed faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceExchange
open Function Finset MeasureTheory Lattice Wilson RG OPE.Therm
open WilsonMeasuredPublicEntranceDeposits WilsonMeasuredPublicEntranceOrder
open scoped Classical BigOperators
variable {I:Type} {G:Gauge} (C:Family G) {N per K f:ℕ}
local notation "X" i:max => Config G (C.side i per)

def remainder (trial:X K→ℂ) (b:I→X K→ℂ) (s:Finset I) (U:X K) :=
  trial U-∏a∈s,b a U

/-- The list is the actual order of replacement of this complete occupied face. -/
theorem original (hC:C.Makes)(live:K≤N)(stop:f≤K)(W:X f)
    (a:I→X N→ℂ)(b:I→X K→ℂ)(s:Finset I)(names:List I)(same:names.Perm s.toList)
    (fund:∀i,funded (a i)) (current:∀i,BoundedAt C (b i)) (trial:X K→ℂ)
    (integral:Integrable (fun U=>(C.path.rep N per K).eval U • trial U) (prior G _)) :
    let y:=fun i=>mean C N (a i) K
    actualTransport C (N:=N) (fun U=>∏i∈s,a i U) (stop.trans live) W-
      actualTransport C (N:=N) trial stop W =
        (∑i∈Ico K N,reading C N a s f i W) +
        ((changes y b (fun _=>1) names).map (fun h=>actualTransport C (N:=N) h stop W)).sum -
        actualTransport C (N:=N) (remainder C trial b s) stop W := by
  intro y
  have convert (j:ℕ)(c:I→X j→ℂ) (U:X j):factors c names U=∏i∈s,c i U:=
    ((same.map (fun i=>c i U)).prod_eq).trans (Finset.prod_map_toList s _)
  have rest : (fun U=>∏i∈s,b i U) = factors b names :=funext fun U=>(convert _ _ U).symm
  have first : singles C N a s K = factors y names :=funext fun U=>(convert _ _ U).symm
  have owned (i:I):BoundedAt C (y i):=by
    obtain ⟨M,meas,pays⟩:=salary C N hC (fund i) (le_refl N) live
    exact ⟨meas,M,pays⟩
  have top:=window C N a s hC fund (le_refl N) stop live W
  rw [first] at top
  have exchanges:=switched C hC live stop W y b owned current names _ (one C)
  simp only [one_mul] at exchanges
  have bought:=WilsonMeasuredPublicEntranceOrder.integrable C hC live (collection C b current names)
  have prior:=congrFun (ActualWilsonAbsoluteTransport.sub C hC live integral bought stop) W
  have returned : remainder C trial b s = fun U=>trial U-factors b names U := by
    funext U
    rw [remainder,convert K b U]
  rw [returned,prior,←exchanges,←top]
  abel

end YM.Integration.WilsonMeasuredPublicEntranceExchange
