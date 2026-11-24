import YM.Integration.WilsonMeasuredPublicEntranceRegisteredFlag
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRestriction
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free PertExtension.Rigidity.Positive
open scoped Classical Topology

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

variable {F:Final C f S}
open XSpace XSpace.Normalize

private theorem faithful {e d:ℕ}(h:e≤d):Function.Injective ((scheme C.labels).rise h):=by
  intro x y eq
  apply (fields C.labels e).injective
  apply Subtype.ext
  exact ((address_rise C.labels d h x).symm.trans (congrArg (address C.labels d) eq)).trans (address_rise C.labels d h y)

open WilsonPhysicalPositionAdmissible (Native)
theorem compatible {J:ℝ→tower S}(lead:Leading F J){A:Type*}{l:Filter A}{r t:A→ℝ}
    (near:Tendsto r l trail)(far:Tendsto (fun i=>t i*r i) l trail)(pos:∀i,0<t i)
    {e d:ℕ}(le:e≤d):∀ᶠi in l,∀v:D e,Frame.cocycle d J (r i) (t i) (pos i) ((scheme C.labels).rise le v)=
      (scheme C.labels).rise le (Frame.cocycle e J (r i) (t i) (pos i) v):=by
  filter_upwards [near.eventually (lead.raised le),far.eventually (lead.raised le)] with i up down v
  apply (Pert.Scale.gearIso C.labels d (t i) (pos i)).injective
  apply (J (r i) d).injective
  change J (r i) d (Pert.Scale.gear C.labels d (t i) (Frame.cocycle d J (r i) (t i) (pos i) ((scheme C.labels).rise le v)))=_
  rw [Frame.cocycle_value]
  change _=J (r i) d (Pert.Scale.gear C.labels d (t i) ((scheme C.labels).rise le (Frame.cocycle e J (r i) (t i) (pos i) v)))
  rw [RG12.Roof.gear_rises,up,Frame.cocycle_value,down]

theorem restrict {J:ℝ→tower S}(lead:Leading F J){A:Type*}{l:Filter A}{r t:A→ℝ}
    (near:Tendsto r l trail)(far:Tendsto (fun i=>t i*r i) l trail)(pos:∀i,0<t i){e k:ℕ}(le:e≤k)
    (Z:Module.End ℂ (D k))(heard:∀v,Tendsto (fun i=>Frame.cocycle k J (r i) (t i) (pos i) v) l (𝓝 (Z v))):
    ∃L:Module.End ℂ (D e),∀v,Tendsto (fun i=>Frame.cocycle e J (r i) (t i) (pos i) v) l (𝓝 (L v)):=by
  let put:(D e)→ₗ[ℂ](D k):=(scheme C.labels).rise le
  obtain ⟨back,undo⟩:=put.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (faithful le))
  refine ⟨back.comp (Z.comp put),fun v=>?_⟩
  apply ((back.continuous_of_finiteDimensional.continuousAt.tendsto).comp (heard (put v))).congr'
  filter_upwards [compatible lead near far pos le] with i hi
  change back (Frame.cocycle k J (r i) (t i) (pos i) ((scheme C.labels).rise le v))=_
  rw [hi]
  exact DFunLike.congr_fun undo _

theorem original {J:ℝ→tower S}(lead:Leading F J){A:Type*}{l:Filter A}[NeBot l]{r t:A→ℝ}
    (near:Tendsto r l trail)(far:Tendsto (fun i=>t i*r i) l trail)(pos:∀i,0<t i){k:ℕ}
    (top:Module.End ℂ (D k))(heard:∀v,Tendsto (fun i=>Frame.cocycle k J (r i) (t i) (pos i) v) l (𝓝 (top v))):
    ∃Z:(d:ℕ)→d≤k→Module.End ℂ (D d),Z k le_rfl=top ∧
      (∀d (hd:d≤k) v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z d hd v))) ∧
      (∀d (hd:d≤k) e (he:e<d)(v:D e),Z d hd ((scheme C.labels).rise he.le v)=
        (scheme C.labels).rise he.le (Z e (he.le.trans hd) v)):=by
  have seats (d:ℕ)(hd:d≤k):=restrict lead near far pos hd top heard
  let Z d hd:=(seats d hd).choose
  have filed d hd:=(seats d hd).choose_spec
  refine ⟨Z,?_,filed,?_⟩
  · apply LinearMap.ext
    intro v
    exact tendsto_nhds_unique (filed k le_rfl v) (heard v)
  · intro d hd e he v
    have pass:=((scheme C.labels).rise he.le).continuous_of_finiteDimensional.continuousAt.tendsto.comp (filed e (he.le.trans hd) v)
    apply tendsto_nhds_unique (filed d hd ((scheme C.labels).rise he.le v))
    apply pass.congr'
    filter_upwards [compatible lead near far pos he.le] with i hi using (hi v).symm

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRestriction
end
