import YM.Integration.WilsonPositionScaleLawIndependent

/-! Equality of the engineering units used by the physical Wilson basis and
by the independent position distribution, including every lower grade. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawUnits
open Function Maxwell Maxwell.Free Extra.FD XSpace XSpace.Normalize FVA2 FVA2.Scale
open WilsonPositionScaleLawHome (Ratio)
open scoped Classical BigOperators
variable {G:Gauge}(F:Labels.Frames G)

theorem address (d:ℕ)(v:(freeTable F).Field d): (fields F d v).val=writes F d v:=by
  obtain ⟨p,rfl⟩:=(freeTable F).onto d v
  rw [fields_eval,writes_project];rfl

private theorem pure {d:ℕ}(B:RStage F d)(i:Fin (B.m+1)):
    let j:Fin (d+1):=⟨(B.w i).1,Nat.lt_succ_of_le (B.cap i)⟩
    Level.proj j (fields F d (B.b i))=fields F d (B.b i):=by
  let j:Fin (d+1):=⟨(B.w i).1,Nat.lt_succ_of_le (B.cap i)⟩
  apply Subtype.ext
  change MvPolynomial.weightedHomogeneousComponent scaleW j.val (fields F d (B.b i)).val=(fields F d (B.b i)).val
  rw [address]
  exact MvPolynomial.weightedHomogeneousComponent_eq_self (B.weighs i)

theorem logUnits (d:ℕ)(s:ℝ)(v:(freeTable F).Field d):
    fields F d (Pert.Scale.gear F d (Real.exp (-s)) v)=Level.Dial d s (fields F d v):=by
  let B:=recorded F d
  let L:=(fields F d).toLinearMap.comp (Pert.Scale.gear F d (Real.exp (-s)))
  let R:=(Level.Dial (G:=G) d s).comp (fields F d).toLinearMap
  have h:L=R:=by
    apply B.b.ext
    intro i
    let j:Fin (d+1):=⟨(B.w i).1,Nat.lt_succ_of_le (B.cap i)⟩
    have same:Level.proj j (fields F d (B.b i))=fields F d (B.b i):=pure F B i
    have dial:=Level.taken (fields F d (B.b i)) s j
    rw [same] at dial
    change fields F d (Pert.Scale.gear F d _ (B.b i))=Level.Dial d s (fields F d (B.b i))
    rw [Pert.Scale.rare,map_smul];exact dial.symm
  exact DFunLike.congr_fun h v

theorem original (d:ℕ)(t:Ratio)(v:(freeTable F).Field d):
    fields F d (Pert.Scale.gear F d t.val v)=Level.Dial d (WilsonPositionScaleLawIndependent.time t) (fields F d v):=by
  rw [←logUnits,WilsonPositionScaleLawIndependent.geometry]

end YM.Integration.WilsonPositionScaleLawUnits
end
