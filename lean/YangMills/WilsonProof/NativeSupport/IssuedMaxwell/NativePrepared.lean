import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NativeWindows
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.NativePrepared
open YM YM.XSpace YM.Maxwell YM.XSpace.Normalize YangMills.MSbar
open Function IssuedMaxwell.Reports
variable {g:YangMills.GaugeGroup} (V:Store g.core)
private theorem joined {d e:ℕ}(F:Sec g.core d→ₗ[ℂ]Sec g.core e)
    (Q:Position.Report (B g) d)(R:Position.Report (B g) e)(hq:Position.Lawful Q)(hr:Position.Lawful R)
    (matching:∀n (t:YM.Test n)(p:Fin n→Sec g.core d),Q n t p= R n t (fun i=>F (p i))):
    received Q hq = recruit F (received R hr):=by
  funext n
  apply LinearMap.ext
  intro t
  apply MultilinearMap.ext
  intro p
  change printed (received Q hq) n t p=printed (received R hr) n t (fun i=>F (p i))
  rw [entire,entire]
  exact matching n t p

theorem original:Position.Prepared (NativeWindows.display V):=by
  refine ⟨NativeWindows.range V,NativeWindows.tangent V,?_,?_⟩
  · intro d Q R hq hr matching p q hp
    have eq:q=step d p:=Subtype.ext hp.symm
    have same:=joined (step d) Q R hq hr (fun n t v=>matching n t v (fun i=>step d (v i)) (fun _=>rfl))
    rw [NativeWindows.lawful V d Q hq,NativeWindows.lawful V (d+1) R hr,same,← V.respects d,eq]
    exact congrArg Subtype.val (fells ((V.measure (d+1)).D (received R hr)) p)
  · intro d Q R hq hr matching p q h
    have eq:q=hinge d p:=(Parity.original p q).mp h
    have same:=joined (hinge d) Q R hq hr (fun n t v=>matching n t v (fun i=>hinge d (v i))
      (fun i=>(Parity.original _ _).mpr rfl))
    rw [NativeWindows.lawful V d Q hq,NativeWindows.lawful V d R hr,same,(V.prepared d).2,eq]
    apply (Parity.original _ _).mpr
    change _=hinge d (hinge d _)
    rw [hinges_back]
    rfl
end IssuedMaxwell.NativePrepared
end
