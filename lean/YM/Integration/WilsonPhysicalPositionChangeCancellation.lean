import YM.Integration.WilsonPhysicalPositionChangePanel

/-! The native finite position solve on a reframed Wilson hierarchy gives
exactly the same fields and every same-horizon target when composed with the
original change. Only leading convergence of that real input change is used. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionChangeCancellation
open Function Filter Set Finset Spec Table Extraction Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped Topology BigOperators Classical
variable {G:Gauge}{d:ℕ}

def cross (A B:Change G d):Change G d:=⟨A.val*B.val,by
  rw [may_change]
  simp only [Module.End.mul_apply]
  exact ⟨by rw [B.property.1,map_zero],
    fun l hl p hp=>A.property.2.1 _ hl _ (B.property.2.1 l hl p hp),
    fun p=>by rw [B.property.2.2.1,A.property.2.2.1],
    fun s p=>by rw [B.property.2.2.2,A.property.2.2.2]⟩⟩

def both (A B:Change G d):Change G d:=A+B+cross A B

theorem action (A B:Change G d):stand (both A B)=(stand A) ∘ₗ (stand B):=by
  ext1 p
  change p+((A.val p+B.val p)+A.val (B.val p))=p+B.val p+A.val (p+B.val p)
  rw [map_add]
  abel

private theorem left_add (a b c:Change G d):cross (a+b) c=cross a c+cross b c:=
  Subtype.ext (add_mul a.val b.val c.val)
private theorem right_add (a b c:Change G d):cross a (b+c)=cross a b+cross a c:=
  Subtype.ext (mul_add a.val b.val c.val)
private theorem left_scale (a b:Change G d)(r:ℝ):cross (r•a) b=r•cross a b:=
  Subtype.ext (smul_mul_assoc r a.val b.val)
private theorem right_scale (a b:Change G d)(r:ℝ):cross a (r•b)=r•cross a b:=
  Subtype.ext (mul_smul_comm r a.val b.val)

def cost (G:Gauge)(d:ℕ):MoveSpace G d→ₗ[ℝ] MoveSpace G d→ₗ[ℝ] MoveSpace G d:=
  LinearMap.mk₂ ℝ (fun a b=>guide G d (cross ((guide G d).symm a) ((guide G d).symm b)))
    (fun _ _ _=>by simp only [map_add,left_add])
    (fun _ _ _=>by simp only [map_smul,left_scale])
    (fun _ _ _=>by simp only [map_add,right_add])
    (fun _ _ _=>by simp only [map_smul,right_scale])

theorem small {I:Type}{l:Filter I}(A B:I→Change G d)
    (a:Tendsto (fun i=>guide G d (A i)) l (𝓝 0))(b:Tendsto (fun i=>guide G d (B i)) l (𝓝 0)):
    Tendsto (fun i=>guide G d (both (A i) (B i))) l (𝓝 0):=by
  let L:MoveSpace G d→L[ℝ] MoveSpace G d→L[ℝ] MoveSpace G d:=(cost G d).toContinuousBilinearMap
  have c:Continuous (fun w:MoveSpace G d×MoveSpace G d=>L w.1 w.2):=
    (L.continuous.comp continuous_fst).clm_apply continuous_snd
  have remainder:Tendsto (fun i=>L (guide G d (A i)) (guide G d (B i))) l (𝓝 0):=by
    simpa only [Function.comp_def,map_zero,zero_apply] using
      (c.tendsto (0,0)).comp (a.prodMk_nhds b)
  have value i:guide G d (cross (A i) (B i))=L (guide G d (A i)) (guide G d (B i)):=by
    change _=guide G d (cross ((guide G d).symm (guide G d (A i))) ((guide G d).symm (guide G d (B i))))
    rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
  simp_rw [both,map_add,value]
  simpa only [zero_add] using (a.add b).add remainder

variable {C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)

theorem original (lead:Leading F J)(V:Store G)(d:ℕ)(A:ℝ→Change G d)
    (near:Tendsto (fun r=>guide G d (A r)) trail (𝓝 0)):
    let P:=WilsonPositionPrescribedScreen.hierarchy F J d
    let Q:=fun r=>recruit (stand (A r)) (P r)
    let B:=fun r=>(V.survey d).firstPass (V.prepared d) (Q r)
    ∀ᶠr in trail,stand (WilsonPositionPrescribedScreen.correction F J V d r)=
      (stand (A r)) ∘ₗ (stand (B r)) ∧
      recruit (stand (WilsonPositionPrescribedScreen.correction F J V d r)) (P r)=
        recruit (stand (B r)) (Q r):=by
  intro P Q B
  obtain ⟨bn,sale⟩:=WilsonPhysicalPositionChangePanel.original F J lead V d A near
  have exactBranch:=WilsonPositionPrescribedScreen.unique F J lead V d (fun r=>both (A r) (B r))
    (small A B near bn)
  filter_upwards [sale,exactBranch] with r bought unique
  have fitted:Fray.SetEq (V.measure d) (both (A r) (B r)) (P r):=by
    change (V.measure d).D (recruit (stand (both (A r) (B r))) (P r))=_
    rw [action,←recruits_comp]
    exact bought.1
  have bound:stand (WilsonPositionPrescribedScreen.correction F J V d r)=(stand (A r)) ∘ₗ (stand (B r)):=
    (congrArg stand (unique.mp fitted)).trans (action ..)
  exact ⟨bound,by rw [bound,←recruits_comp]⟩

end YM.Integration.WilsonPhysicalPositionChangeCancellation
end
