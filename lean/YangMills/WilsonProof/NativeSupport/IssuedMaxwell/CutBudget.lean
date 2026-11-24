import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CutOdd
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.CutBudget
open YM YM.XSpace YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick
open YM.XSpace.Normalize YM.XSpace.Structure1 YM.XSpace.Cirrus YM.XSpace.Future YM.XSpace.AxesTangent YM.XSpace.Photo
open scoped Classical
variable (G:Gauge)(d:ℕ)(c:Shade.Cut)

theorem original (g:G.Simple)(hd:4≤d):Manages c G d:=by
  classical
  let read (p:CutOdd.Station G d c):=showCase p.val
  obtain ⟨s,u,complete⟩:=bought read (CutOdd.original G d c g hd)
  let incl:CutOdd.Station G d c ↪ PotLin G d:=⟨Subtype.val,Subtype.val_injective⟩
  let T:=s.map incl
  let pick (i:s):T:=⟨i.val.val,Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩⟩
  have one:Function.Injective pick:=by
    intro i j h
    have equal:i.val.val=j.val.val:=congrArg (fun a:T=>a.val) h
    exact Subtype.ext (Subtype.ext equal)
  have onto:Function.Surjective pick:=by
    intro j
    obtain ⟨k,hk,h⟩:=Finset.mem_map.mp j.property
    exact ⟨⟨k,hk⟩,Subtype.ext h⟩
  let e:s≃T:=Equiv.ofBijective pick ⟨one,onto⟩
  refine ⟨T,fun j=>u (e.symm j),?_,?_⟩
  · intro x
    calc
      x=∑i:s,read i.val x • u i:=complete x
      _=∑i:T,showCase i.val x • u (e.symm i):=by
        apply Fintype.sum_equiv e
        intro a
        have he:(e a).val=a.val.val:=rfl
        simp only [he,e.symm_apply_apply,read]
  · intro j
    obtain ⟨k,hk,h⟩:=Finset.mem_map.mp j.property
    have eq:k.val=j.val:=h
    exact eq ▸ k.property
end IssuedMaxwell.CutBudget
end
