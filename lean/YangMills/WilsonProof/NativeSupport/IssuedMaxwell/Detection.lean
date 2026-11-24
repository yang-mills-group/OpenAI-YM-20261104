import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Sectors
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Detection
open YM YM.Maxwell YM.Extra.FD
variable (g:YangMills.GaugeGroup)

theorem original (d:ℕ)(p:shellSector g.core d):
    (∀ n (w:Fin n→Σ e,shellSector g.core e)(x:YM.Points (n+1)),
      x∈YangMills.separated _→Wick.moment g.core x (Fin.cons p.val (fun i=>(w i).2.val))=0) ↔ p=0:=by
  constructor
  · intro h
    have hn:p∈residual g.core d:=by
      change LinearMap.pi (fun v:ProbeFamily g.core=>v.test d) p=0
      funext v
      change v.test d p=0
      rw [test_formula]
      exact h v.n (fun i=>⟨v.d i,v.exterior i⟩) v.x v.clear
    rwa [no_residual,Submodule.mem_bot] at hn
  · rintro rfl n w x hx
    let v:ProbeFamily g.core:=⟨n,fun i=>(w i).1,fun i=>(w i).2,x,hx⟩
    exact (test_formula v d 0).symm.trans (map_zero (v.test d))
end IssuedMaxwell.Detection
end
