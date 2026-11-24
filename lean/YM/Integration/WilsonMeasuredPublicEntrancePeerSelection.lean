import YM.Integration.WilsonMeasuredPublicEntranceTrialLamp
import YM.Integration.WilsonMeasuredPublicEntrancePeerFace

/-! Put the native returned ordinary trial peers and the actual cropped
physical peers on one filed gallery. The individual occurrence keys of
either class remain available on the resulting gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePeerSelection
open Function Finset Lattice Wilson RG Marker QuadraticLocal
open WilsonMeasuredPublicEntranceLampFamily WilsonMeasuredPublicEntranceTrialLamp
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V I X:Type}[DecidableEq V][Fintype V]
    (W:Rep G n)(o:V → Site n)(J:Census V)

omit [Fintype V] in
private theorem own {K:Type} (L:Lamps Unit K G W.p o J):Kept W o J L L:=
  ⟨id,injective_id,fun _=>⟨rfl,rfl,rfl,fun _=>rfl⟩⟩

omit [Fintype V] in
private theorem chain {K K' K'':Type} {A:Lamps Unit K G W.p o J} {B:Lamps Unit K' G W.p o J}
    {C:Lamps Unit K'' G W.p o J} (u:Kept W o J A B)(v:Kept W o J B C):Kept W o J A C:=by
  obtain ⟨a,inj,info⟩:=u
  obtain ⟨b,inj',info'⟩:=v
  refine ⟨b ∘ a,inj'.comp inj,fun i=>?_⟩
  obtain ⟨mo,atSite,lit,term⟩:=info i
  obtain ⟨mo',atSite',lit',term'⟩:=info' (a i)
  exact ⟨mo'.trans mo,atSite'.trans atSite,lit'.trans lit,fun t=>(term' t).trans (term t)⟩

theorem original [Countable I](E:Lamps X I G W.p o J)(x:X)(trial:Finset V)
    {K:V→Type}[∀v,Countable (K v)](crop:(v:V)→Lamps Unit (K v) G W.p o J)
    (w:V→ℝ)(wp:∀v,0<w v){α r:ℝ}(ap:0≤α)(spent:E.Paid w W.p.B α r)
    (c:V→ℝ)(fare:∀v,(crop v).Paid w W.p.B α (c v))(lane:∀v k,(crop v).mode k=J.fire v)
    (field:V → Config G n → ℂ)(seen:∀v U,((crop v).log () U).part (J.fire v)=field v U):
    let price:=fun v=>if v∈trial then r else c v
    let signed:=fun v U=>if v∈trial then (E.log x U).part (J.fire v) else field v U
    ∃ (K':Type) (_:Countable K') (P:Lamps Unit K' G W.p o J),
      P.Paid w W.p.B α (∑v,price v) ∧
      (∀U,P.log () U=∑v,Poly.send (J.fire v) (signed v U)) ∧
      (∀v (s:J.Mode),v∈s.val→∀U,WilsonMeasuredCompanionFace.peers P v s () U=
        ∏u∈s.val.erase v,signed u U) ∧
      (∀v∈trial,Kept W o J (leaf E v x) P) ∧ ∀v∉trial,Kept W o J (crop v) P:=by
  classical
  intro price signed
  have roster(v:V):∃(S:Type)(_:Countable S)(P:Lamps Unit S G W.p o J), P.Paid w W.p.B α (price v) ∧
      (∀s,P.mode s=J.fire v) ∧ (∀U,(P.log () U).part (J.fire v)=signed v U) ∧
      (v∈trial→Kept W o J (leaf E v x) P) ∧ (v∉trial→Kept W o J (crop v) P):=by
    by_cases yes:v∈trial
    · refine ⟨_,inferInstance,leaf E v x,?_,lanes E v x,?_,fun _=>own W o J _,by simp [yes]⟩
      · simpa only [price,if_pos yes] using paid E v x spent
      · intro U
        rw [read E v x wp ap spent,Poly.part_send,if_pos rfl]
        simp only [signed,if_pos yes]
    · exact ⟨_,inferInstance,crop v,by simpa only [price,if_neg yes] using fare v,
        lane v,fun U=>by simpa only [signed,if_neg yes] using seen v U,by simp [yes],fun _=>own W o J _⟩
  choose S count P expen key val yes no using roster
  letI(v:V):Countable (S v):=count v
  obtain ⟨K',cnt,out,charge,test,retain⟩:=WilsonMeasuredPublicEntranceLampFamily.original W o J P w wp α ap price expen key
    (fun _ U v=>signed v U) (fun v _=>val v) univ
  exact ⟨K',cnt,out,charge,test (),fun v s hv U=>WilsonMeasuredPublicEntrancePeerFace.original out v s hv () U _ (test () U),
    fun v hv=>chain W o J (yes v hv) (retain v (mem_univ v)),
    fun v hv=>chain W o J (no v hv) (retain v (mem_univ v))⟩

end YM.Integration.WilsonMeasuredPublicEntrancePeerSelection
end
