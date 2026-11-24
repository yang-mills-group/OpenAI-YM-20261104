import YM.Integration.WilsonMeasuredPublicEntranceNativeChange
import YM.Integration.WilsonPhysicalPositionBornTransition

/-! The measured unscaled transfer on the two actual endpoint fields converges
to the scaled position cocycle, also when the submitted finite field varies. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeArrow
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open scoped Topology ContDiff Classical BigOperators
open WilsonMeasuredPublicEntranceNativeChange
open private engine from YM.Integration.WilsonPhysicalPositionBornTransition
variable {G:Gauge}{C:Family G}{S:Table C.book}
local notation "D" => Table.Field (Bel C.book)

theorem held {I:Type*}{l:Filter I}{U J:ℝ→tower S}(aligned:localCost trail U J)
    {r t:I→ℝ}{s:ℝ}(hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(positive:∀i,0<t i)
    {d:ℕ}(Z:Module.End ℂ (D d))
    (heading:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (positive i) v) l (𝓝 (Z v)))
    {v:I→D d}{z:D d}(filed:Tendsto v l (𝓝 z)):
    Tendsto (fun i=>(U (r i) d).symm (U (t i*r i) d (v i))) l
      (𝓝 (Pert.Scale.gear C.labels d s (Z z))):=by
  have travel:Tendsto (fun i=>t i*r i) l trail:=by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [mul_zero] using ht.mul (hr.mono_right nhdsWithin_le_nhds)
    filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi using mul_pos (positive i) hi
  let w i:=change J U (t i*r i) d (v i)
  have ballot:Tendsto w l (𝓝 z):=
    Dash.arcing ((directions aligned d).2.comp travel) filed
  let raw i:=Frame.cocycle d J (r i) (t i) (positive i) (w i)
  have ticket:Tendsto raw l (𝓝 (Z z)):=
    Dash.arcing (Dash.fit_plane (fun i=>(Frame.cocycle d J (r i) (t i) (positive i)).toLinearMap) Z heading) ballot
  have adjusted:=engine (C:=C) ht ticket
  have arrival:=Dash.arcing ((directions aligned d).1.comp hr) adjusted
  apply arrival.congr'
  refine .of_forall fun i=>?_
  change (U (r i) d).symm (J (r i) d
    (Pert.Scale.gear C.labels d (t i) (Frame.cocycle d J (r i) (t i) (positive i) (w i))))=_
  rw [Frame.cocycle_value]
  simp [w,WilsonMeasuredPublicEntranceNativeChange.change]

private theorem reversed {d:ℕ}{t:ℝ}(pos:0<t)(z:D d):
    (Pert.Scale.gearIso C.labels d t pos).symm z=Pert.Scale.gear C.labels d t⁻¹ z:=by
  have pay:Pert.Scale.gear C.labels d t ((Pert.Scale.gearIso C.labels d t pos).symm z)=z:=
    (Pert.Scale.gearIso C.labels d t pos).apply_symm_apply z
  have inv:=Pert.Scale.gear_inverse C.labels pos.ne' ((Pert.Scale.gearIso C.labels d t pos).symm z)
  rw [pay] at inv
  exact inv.symm

theorem original {I:Type*}{l:Filter I}{U J:ℝ→tower S}(aligned:localCost trail U J)
    {r t:I→ℝ}{s:ℝ}(hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(hs:0<s)(positive:∀i,0<t i)
    {d:ℕ}(Z:Module.End ℂ (D d))
    (heading:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (positive i) v) l (𝓝 (Z v)))
    {v:I→D d}{z:D d}(filed:Tendsto v l (𝓝 z)):
    Tendsto (fun i=>(Pert.Scale.gearIso C.labels d (t i) (positive i)).symm
      ((U (r i) d).symm (U (t i*r i) d (v i)))) l (𝓝 (Z z)):=by
  have full:=held aligned hr ht positive Z heading filed
  have priced:=engine (C:=C) (ht.inv₀ hs.ne') full
  have refund:=Pert.Scale.gear_inverse C.labels hs.ne' (Z z)
  simp only [reversed]
  simpa only [refund] using priced

end YM.Integration.WilsonMeasuredPublicEntranceNativeArrow
end
