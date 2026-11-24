import YM.Integration.WilsonMacroscopicRichReflectedRoster

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSeparateScales
open YM YM.Spec YM.PhysMS YM.Trace.Pilot YM.Word YM.Table.Pairing YM.Spin YM.Climb YM.Next.UVStress YM.OPE YM.OPE.Orbits
open Filter Set WilsonMacroscopicRichReflectedRoster
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Spec.Final C f S)
variable (J:ℝ→tower S)(H:Leading F J)

private theorem dilated {n:ℕ}{x:Points n}{a:Axis}(h:single x a){r:ℝ}(hr:0<r):single (r•x) a:=by
  refine ⟨fun _ _ e=>h.1 ((smul_right_injective _ hr.ne') e),fun i=>mul_pos hr (h.2 i)⟩

include H in
/-- The two independently chosen physical radii lie in one common neighbourhood. Both complete
field rosters can therefore move simultaneously outside every modulus for one fixed relative scale. -/
theorem original {n m:ℕ}(a:Axis)(v:Fin n→(Bel C.book).Tag)(w:Fin m→(Bel C.book).Tag)
    (K:Set (Points n))(L:Set (Points m))(hK:IsCompact K)(hL:IsCompact L)
    (xSide:∀x∈K,single x a)(ySide:∀y∈L,single y a):
    ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,∀x∈K,∀y∈L,
      ‖S.useAt S (closedUp a (r•x) (τ•y))
        (Fin.append (fun i=>physical J r (v i)) (fun j=>physical J τ (w j)))‖≤B:=by
  let u:=reflected a ∘ v
  obtain ⟨A,hA,near⟩:=WilsonMacroscopicRichReflectedRoster.original F J H a u K hK xSide
  obtain ⟨D,hD,far⟩:=WilsonMacroscopicRichReflectedRoster.original F J H a w L hL ySide
  have phase:∀ᶠr in trail,∀i,realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r (u i).1):=
    Filter.eventually_all.2 (fun i=>H.equivariant (u i).1)
  let U: Set ℝ:={r|0<r ∧ (∀x∈K,‖S.gram a (realize (labels J u r) (r•x)) (realize (labels J u r) (r•x))‖≤A) ∧
    (∀y∈L,‖S.gram a (realize (labels J w r) (r•y)) (realize (labels J w r) (r•y))‖≤D) ∧
    ∀i,realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r (u i).1)}
  refine ⟨Real.sqrt A*Real.sqrt D,by positivity,U,?_,?_⟩
  · filter_upwards [self_mem_nhdsWithin,near,far,phase] with r hp h k c using ⟨hp,h,k,c⟩
  intro r hr τ hτ x hx y hy
  have p:=dilated (xSide x hx) hr.1
  have q:=dilated (ySide y hy) hτ.1
  have gram:=WilsonMacroscopicRichTwoLengthSlates.paired F a
    ⟨realize (labels J u r) (r•x),living _ p⟩ ⟨realize (labels J w τ) (τ•y),living _ q⟩
  have cash:‖S.gram a (realize (labels J u r) (r•x)) (realize (labels J w τ) (τ•y))‖≤Real.sqrt A*Real.sqrt D:=
    gram.trans (mul_le_mul (Real.sqrt_le_sqrt (hr.2.1 x hx)) (Real.sqrt_le_sqrt (hτ.2.2.1 y hy)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [displacement S F.room.kernel.laws.toSymmetric _ _ p q,
    ←S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (spans p q),joined F J a u w r τ hr.2.2.2] at cash
  simpa only [u,Function.comp_apply,twice] using cash

end YM.Integration.WilsonMacroscopicRichSeparateScales
