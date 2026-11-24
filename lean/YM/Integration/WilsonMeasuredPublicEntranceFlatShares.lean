import YM.Integration.WilsonMeasuredPublicEntranceFlatLine
import YM.Integration.WilsonMeasuredPublicEntranceShareRoster
import YM.Integration.WilsonMeasuredPublicEntrancePeerTests
/-! Ordered hard contacts at the genuine older marginal. The full signed
cofactor uses the original fields at the other occupied sites. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceFlatShares
open Function Finset MeasureTheory Lattice RG Wilson
open PhysicalNext PhysicalNext.Repeat Legato WilsonThermometerUnitFilingCoarse
open WilsonMeasuredPublicEntranceFlatLine WilsonMeasuredPublicEntranceOrder
open WilsonMeasuredPublicEntrancePeerShares WilsonMeasuredPublicEntranceCheapOrder
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V]{N p f b:ℕ}(s:Finset V)
local notation "cfg" => Config G (R.family.side f p)
variable (x y e:V → Config G (R.family.side f p) → ℂ)
def rest (m:Share V)(i:V)(U:cfg):ℂ:=
  WilsonMeasuredPublicEntranceShareRoster.field m (fun i=>x i U) (fun i=>y i U) (fun i=>e i U) i
def owned (h:V → cfg → ℂ)(m:Share V)(U:cfg):ℂ:=
  h m.atName U*∏i∈s.erase m.atName,rest R x y e m i U
def contact (a c z:V → cfg → ℂ)(U:cfg):ℂ:=
  WilsonMeasuredPublicEntranceCheapOrder.route (fun i=>y i U) (fun i=>x i U-e i U) (fun i=>a i U-c i U-z i U) s.toList
omit [DecidableEq V] in
private theorem list_price {I:Type}(xs:List I)(v:I → ℂ)(K:ℝ)(billed:∀i∈xs,‖v i‖ ≤ K):
    ‖(xs.map v).sum‖ ≤ (xs.length:ℝ)*K:=by
  induction xs with
  | nil=>simp
  | cons i ts ih=>
    have first:=billed i (List.mem_cons_self ..)
    have tail:=ih (fun j h=>billed j (List.mem_cons_of_mem _ h))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    linarith only [first,tail,norm_add_le (v i) (ts.map v).sum]

theorem original (bf:b ≤ f)(a c z:V → cfg → ℂ)
    (xpay:∀i,BoundedAt R.family (x i))(ypay:∀i,BoundedAt R.family (y i))
    (epay:∀i,BoundedAt R.family (e i))(af:∀i,BoundedAt R.family (a i))
    (cf:∀i,BoundedAt R.family (c i))(zf:∀i,BoundedAt R.family (z i))
    (A C Z:ℝ)(tax:∀m∈shares s.toList,
      ‖reading R (N:=N) (owned R s x y e a m) b bf‖ ≤ A ∧
      ‖reading R (N:=N) (owned R s x y e c m) b bf‖ ≤ C ∧
      ‖reading R (N:=N) (owned R s x y e z m) b bf‖ ≤ Z):
    let F:=contact R s x y e a c z
    Integrable F (prior G _) ∧
      ‖reading R (N:=N) F b bf‖ ≤ ((shares s.toList).length:ℝ)*(A+C+Z):=by
  intro F
  have peer (m:Share V)(i:V):BoundedAt R.family (rest R x y e m i):=by
    unfold rest WilsonMeasuredPublicEntranceShareRoster.field WilsonMeasuredPublicEntranceShareRoster.head
    split_ifs
    · exact ypay i
    · exact epay i
    · exact xpay i
  let H (h:V → cfg → ℂ)(hpay:∀i,BoundedAt R.family (h i))(m:Share V):films G (R.family.side f p):=
    ⟨owned R s x y e h m,WilsonMeasuredPublicEntrancePeerTests.dressed R (h m.atName) (hpay _)
      (rest R x y e m) (peer m) (s.erase m.atName)⟩
  let rows (m:Share V):films G (R.family.side f p):=
    weight (fun _=>(1:ℂ)) m • (H a af m-H c cf m-H z zf m)
  have whole (U:cfg):F U=((shares s.toList).map (fun i=>(rows i).val U)).sum:=by
    change WilsonMeasuredPublicEntranceCheapOrder.route _ _ _ _=_
    have issued:=WilsonMeasuredPublicEntrancePeerShares.original (fun i=>x i U) (fun i=>y i U) (fun i=>e i U)
      (fun _=>(1:ℂ)) (fun i=>a i U-c i U-z i U) s.toList
    simp only [one_mul] at issued
    rw [issued]
    apply congrArg List.sum
    apply List.map_congr_left
    intro m chosen
    have prior:=WilsonMeasuredPublicEntranceShareRoster.original s m chosen (fun i=>x i U) (fun i=>y i U) (fun i=>e i U)
    change WilsonMeasuredPublicEntrancePeerShares.weight (fun _=>(1:ℂ)) m*((a m.atName U-c m.atName U-z m.atName U)*peers _ _ _ m)=
      WilsonMeasuredPublicEntrancePeerShares.weight (fun _=>(1:ℂ)) m*(owned R s x y e a m U-owned R s x y e c m U-owned R s x y e z m U)
    rw [prior.2]
    unfold owned rest
    ring
  obtain ⟨paid,file⟩:=assembled R N p f b bf (shares s.toList) rows F whole
  refine ⟨paid,?_⟩
  rw [file]
  apply list_price
  intro m present
  obtain ⟨aa,cc,zz⟩:=tax m present
  change ‖ear R N p f b bf (WilsonMeasuredPublicEntrancePeerShares.weight (fun _=>(1:ℂ)) m • (H a af m-H c cf m-H z zf m))‖ ≤ _
  rw [map_smul,map_sub,map_sub,smul_eq_mul,norm_mul,WilsonMeasuredPublicEntranceShareRoster.sign,one_mul]
  exact (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add aa cc)) zz)

end YM.Integration.WilsonMeasuredPublicEntranceFlatShares
end
