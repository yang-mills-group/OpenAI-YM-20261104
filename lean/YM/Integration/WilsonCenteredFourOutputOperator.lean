import YM.Integration.WilsonCenteredFourOutputForecast

/-! An original normalized output measurement pays the physical positive
coefficient with its full engineering power, on the elected single ticket. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputOperator
open Filter Set Spec Table Climb Extraction Trace Trace.Pilot Trace.Terrace
open GapsContact GapsContact.Ascent GapsContact.Seams Frontier6 OPE OPE.Orbits OPE.Log
open PhysicalNext.Repeat.Legato Next.UVStress PhysMS RG17 WilsonCenteredFourOutputSensor
open FVA2 FVA2.Scale FVA2.Register FVA2.O FVA2.O.Score MS MS.Land MS.Fleet
open XSpace XSpace.Normalize
open scoped Topology Classical
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S) {simple:G.Simple} {l:Ultrafilter (ℕ×ℕ)} {a:Arch R.family}
    {Y:(Bel R.family.book).Hierarchy} (bliss:Bliss F l a Y)
    (ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _))
    (V:Store G) (lead:Leading F J) (c:Q.channels 4)

def row (r:ℝ) : RG17.Free R.family 4 →L[ℂ] ℂ :=
  ((grade F Q c).toLinearMap.comp (J r 4).toLinearMap).toContinuousLinearMap

include simple bliss ticket V lead in
theorem original: ∃ k:ℕ,∃C:ℝ,0≤C ∧ ∀ᶠr in trail,‖row F Q J c r‖≤C*dock r^k*r^4:=by
  obtain ⟨K,k,kp,priced⟩:=WilsonCenteredFourOutputForecast.ticket F Q (simple:=simple) bliss ticket c
  obtain ⟨W,wp,unit⟩:=WilsonNormalizedReflectedForm.uniform F J V lead 4 zero_le_one
  refine ⟨k,K*W,mul_nonneg kp wp,?_⟩
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [priced,unit,small,self_mem_nhdsWithin] with r cost bounded small pos
  have dk:0≤dock r:=zero_le_one.trans (dock_valid r ⟨pos,small⟩)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x one
  have cash:Ascent.cost F 4 r (J r 4 x)≤W:=bounded false x one.le
  exact (cost _).trans ((mul_le_mul_of_nonneg_left cash (by positivity)).trans_eq (by ring))

include simple bliss ticket V lead in
theorem paid: ∃ k:ℕ,∃C:ℝ,0≤C ∧ ∀ᶠr in trail,∀(x:S.Field 4)(v:RG17.Free R.family 4),
    ‖grade F Q c x-grade F Q c (J r 4 v)‖ ≤ C*dock r^k*r^4*‖(J r 4).symm x-v‖:=by
  obtain ⟨k,C,cp,priced⟩:=original F Q J (simple:=simple) bliss ticket V lead c
  refine ⟨k,C,cp,priced.mono fun r h x v=>?_⟩
  let z:=(J r 4).symm x-v
  have ears:row F Q J c r z=grade F Q c x-grade F Q c (J r 4 v):=by
    change grade F Q c (J r 4 ((J r 4).symm x-v))=_
    rw [map_sub,LinearEquiv.apply_symm_apply,map_sub]
  rw [←ears]
  exact ((row F Q J c r).le_opNorm z).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

include simple bliss ticket V lead in
theorem packet: ∃ k:ℕ,∃C:ℝ,0≤C ∧ ∀ᶠr in trail,∀(x:Fin 2→E4)(o:E4)
    (v:Fin 2→RG17.Free R.family 4)(y:RG17.Free R.family 4),
    let u:Fin 2→S.Field 4:= fun i=>J r 4 (v i)
    ‖Q.coef 4 c x (d:=fun _:Fin 2=>4) u o-grade F Q c (J r 4 y)‖≤
      C*dock r^k*r^4*‖(J r 4).symm (Q.packet 4 x (d:=fun _:Fin 2=>4) u o)-y‖:=by
  obtain ⟨k,C,cp,priced⟩:=paid F Q J (simple:=simple) bliss ticket V lead c
  refine ⟨k,C,cp,?_⟩
  filter_upwards [priced] with r bill x o v y u
  rw [←WilsonCenteredFourOutputSensor.packet F Q c x (d:=fun _:Fin 2=>4) u o]
  exact bill _ _

end YM.Integration.WilsonCenteredFourOutputOperator
