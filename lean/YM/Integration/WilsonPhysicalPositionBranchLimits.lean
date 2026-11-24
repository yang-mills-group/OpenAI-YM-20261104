import YM.Integration.WilsonPhysicalPositionCocycleNative

/-! Every limit, including a limit at a switch of reporting dates, is in
the finite elected set. This supplies the compactness half of the physical
mixed-scale branch test. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionBranchLimits
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionAdmissible
open WilsonPhysicalPositionBornCandidates (operator)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

theorem closed {d:ℕ}{I:Type*}{l:Filter I}[NeBot l]{Y:I→D d→ₗ[ℂ]D d}{Z:D d→ₗ[ℂ]D d}
    (hy:∀ᶠ i in l,Native C (Y i))(hz:∀v,Tendsto (fun i=>Y i v) l (𝓝 (Z v))):Native C Z:=by
  constructor
  · exact tendsto_nhds_unique (hz _)
      (tendsto_const_nhds.congr' (hy.mono fun i h=>h.neutral.symm))
  · intro j hj v
    exact (LinearMap.range ((scheme C.labels).rise hj)).closed_of_finiteDimensional.mem_of_tendsto (hz _)
      (hy.mono fun i h=>h.lower hj v)
  · intro v
    exact tendsto_nhds_unique ((hz _).congr' (hy.mono fun i h=>h.conjugate v))
      ((Spin.cont_conj (spin_free C.labels) d).continuousAt.tendsto.comp (hz v))
  · intro s v
    exact tendsto_nhds_unique ((hz _).congr' (hy.mono fun i h=>h.orientation s v))
      (((Bel C.book).mirror (spin_free C.labels) d s).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hz v))

theorem chart (lead:Leading F J){I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(_hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    {d:ℕ}(Z:D d→ₗ[ℂ]D d)
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v))):
    ∃a:MoveSpace G d,WilsonPhysicalPositionBornTransition.present (C:=C)
      (WilsonPhysicalPositionDiscreteBranches.field a)=Z:=by
  have hrt:Tendsto (fun i=>t i*r i) l trail:=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa only [mul_zero] using ht.mul (hr.mono_right nhdsWithin_le_nhds)
    filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi using mul_pos (pos i) hi
  apply coordinates C
  apply closed (Y:=fun i=>(Frame.cocycle d J (r i) (t i) (pos i)).toLinearMap) _ conv
  filter_upwards [hr.eventually (WilsonPhysicalPositionCocycleNative.purchased F J lead d),
    hrt.eventually (WilsonPhysicalPositionCocycleNative.purchased F J lead d)] with i q v
  exact WilsonPhysicalPositionCocycleNative.original F J (pos i) q v

theorem original (lead:Leading F J)(V:Store G)(d:ℕ):
    ∃ menu:Finset (MoveSpace G d),∀{I:Type*}{l:Filter I}[NeBot l]
      {r t:I→ℝ}{c u:ℝ},0<c→0<u→Tendsto r l trail→Tendsto t l (𝓝 u)→
      (∀ᶠ i in l,t i∈Icc c 1)→∀(pos:∀i,0<t i)(Z:D d→ₗ[ℂ]D d),
      (∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))→
      ∃a∈menu,WilsonPhysicalPositionBornTransition.present (C:=C) (WilsonPhysicalPositionDiscreteBranches.field a)=Z:=by
  obtain ⟨_,_,menu,ear⟩:=WilsonPhysicalPositionPhysicalBranches.original F J lead V d
  refine ⟨menu,?_⟩
  intro I l hl r t c u hc hu hr ht hi pos Z conv
  obtain ⟨a,ha⟩:=chart F J lead hr hu ht pos Z conv
  refine ⟨a,ear hc hu hr ht hi pos a (fun v=>?_ ),ha⟩
  change Tendsto _ l (𝓝 ((WilsonPhysicalPositionBornTransition.present (C:=C)
    (WilsonPhysicalPositionDiscreteBranches.field a)) v))
  rw [ha];exact conv v

end YM.Integration.WilsonPhysicalPositionBranchLimits
end
