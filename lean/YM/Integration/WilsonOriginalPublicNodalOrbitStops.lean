import YM.Integration.WilsonIndependentRawRosterOrbit

/-! The nonconstant income of a complete entered word at every later page of a single approved stop. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalOrbitStops
open Function Lattice RG Source Labels PertExtension XSpace
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open WilsonIndependentRawRosterOrbit (report)
open WilsonIndependentRawRosterWord (body degree enrolled)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{J I:Type}{M:J→ℕ}{n:Page M→Side}{S:Heir n G}{V:Reel S}{T:S.Accounts}
    {Γ:Flap M→Layer (Foot G) (Foot G)}{B:Flap M→Bride G}{p b u:ℕ}
    {D:Choice M}{L:Meter J}{cash:Flap M→ℝ≥0∞}{γ:ℝ}
    (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(σ:I→Bool)(d:I→ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)(sites:J→I → Cover)
    (A:Cylinder V T Γ B L cash p b u)(lantern:Lantern S D L cash γ)
    (x:J→Room)(start:∀w,S.l (Page.opening M w)=1)
    (fare:∀w,ENNReal.ofReal (1+WilsonIndependentRawRosterBudget.span (x w) (sites w) arms)≤L.val w)

include A lantern start fare

theorem original (stop:Choice M)(old:D.age ≤ stop.age)(q:ℕ)(hq:q≤p):
    ∃C:ℝ,∃k:ℕ,0≤C ∧ ∀v:Page stop.after.spans,
      ‖note ((report R W σ d key arms T sites).main (stop.after.page v) q 0)-
        note ((report R W σ d key arms T sites).main (stop.choose v.bindW) q 0)‖ ≤
      C*(L.val v.bindW).toReal^k*(S.l (stop.choose v.bindW)^γ)⁻¹:=by
  let Z:=report R W σ d key arms T sites
  have seed:=WilsonIndependentRawRosterOrbit.opening R W σ d key arms T sites V L x p (u+b+b) start fare
  have light:=A.leads lantern
  have hk:14≤quantum b u:=by have h:=A.positive; unfold quantum; omega
  have high:u+b+b≤quantum b u:=by unfold quantum;omega
  have ward:=A.rates.preWard A.inspiration T Z (fun w=>body R W σ d key arms (sites w)) A.bulk A.price
    hk A.port (fun w=>(enrolled R W σ d key arms (sites w)).1)
  have early:=WilsonIndependentRawWordTransport.early Z A.creators A.bulk light.lead high seed
    (fun _=>ENNReal.one_ne_top) ward D
  have raw:=S.appear T Z light early ward (fun _ _ _ _ _ h=>by omega) (fun _=>ENNReal.one_ne_top)
  have soft:=S.warmer light
  have H:S.Bend T Z (u+b+b) p stop x (S.softnessWeight γ) 1 1 L:=
    {raw with young:=fun i hi r hr=>S.success T Z A.creators A.bulk soft raw high old hi hr}
  let E:=stop.after
  have paid:Carry (coverL E.spans L) (fun v=>ticket (S.softnessWeight γ ∘ E.page) 1 (Page.opening E.spans v.bindW))
      (fun v=>‖note (Z.main (E.page v) q 0)-note (Z.main (stop.choose v.bindW) q 0)‖ₑ):=
    (E.expanse S).till _ (fun v=>Z.main (E.page v)) (E.sector S A.creators) (E.getN S A.bulk A.creators)
      (E.credit S soft) (S.saddle T Z A.creators H) high hq
  have cur: (fun v:Page E.spans=>ticket (S.softnessWeight γ ∘ E.page) 1 (Page.opening E.spans v.bindW))=
      fun v=>ENNReal.ofReal (S.l (stop.choose v.bindW)^γ)⁻¹:=by
    funext v
    change 1*(ENNReal.ofReal (S.l (stop.choose v.bindW)^γ))⁻¹=_
    rw [one_mul,ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (S.hl _) _)]
  rw [cur] at paid
  exact Centered.Carry_rt (fun w=>inv_nonneg.mpr (Real.rpow_pos_of_pos (S.hl _) _).le) paid

end YM.Integration.WilsonOriginalPublicNodalOrbitStops
end
