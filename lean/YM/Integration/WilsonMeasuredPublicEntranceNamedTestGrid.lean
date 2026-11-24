import YM.Integration.WilsonMovingForkPositionWage

/-! Interpolate a submitted finite continuum field on the actual optical mesh after its own spectral costs are accounted for. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNamedTestGrid
open Function Filter Finset Set Metric Extraction Table Spec PhysMS Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedGridTree WilsonSeparatedPhysicalRay WilsonSeparatedBranchStencil
open PhysicalNext.Repeat.Legato FVA2.Scale
open WilsonPositionHomogeneousFrame FVA2 FVA2.Register MS MS.Land RG17
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}(J:ℝ→tower S)(Z:WilsonPrescription G)
  {l:Ultrafilter (ℕ×ℕ)}{z:Trace.Terrace.Arch R.family}

theorem original (simple:G.Simple)(bliss:Bliss F l z H){n:ℕ}(d:Fin n→ℕ)
    {η:ℝ}(ep:0<η)(h P:ℕ)(E:Type)[Fintype E]:
    ∃m:ℕ,∃C:ℝ,0≤C ∧ ∀ᶠr in trail,∀ref:E→E4,∀v:(i:Fin n)→S.Field (d i),∀D:ℝ,
      (∏i,Ascent.cost F (d i) r (v i))*(wilson z r)^h≤D →
      ∀δ:ℝ,∀dp:0<δ,δ≤(wilson z r)^2 → ∀X:Points n,(∀i j,i≠j → η≤dist (X i) (X j)) →
      let T:=sold m ref dp X
      let field:=fun x:Points n=>S.classMoment S d (r • x) v
      ‖field X-read T field‖≤C*D*(wilson z r)^P:=by
  let g:=wilson z
  have hg:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨ν,vp,p,paid⟩:=WilsonMovingForkGridPrice.original (E:=E) F simple bliss d ep
  let m:=P+2*p+h
  have power:P+2*p+h≤2*(m+1):=by dsimp [m];omega
  obtain ⟨Δ,dop,A,ap,quad⟩:=paid m
  let c:=G.slopeConstant⁻¹+1
  have cp:0<c:=by dsimp [c];positivity [Gauge.slopeConstant_pos simple]
  have head:0≤A*(c/ν)^p:=mul_nonneg ap (pow_nonneg (div_nonneg cp.le vp.1.le) _)
  refine ⟨m,A*(c/ν)^p,head,?_⟩
  have dorm:=((hg.conforms simple).pow 2).eventually (ge_mem_nhds (by simpa using dop: (0:ℝ)^2<Δ))
  have trailpos:=hg.running.eventually (ge_mem_nhds (by dsimp [c];linarith:G.slopeConstant⁻¹<c))
  filter_upwards [quad,dorm,trailpos,hg.positive,(hg.conforms simple).eventually
    (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin,(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds]
    with r read tiny logbill gp g1 (rp:0<r) (r1:r≤1)
  intro ref v D salary δ dp mesh X sep T field
  have gn:0≤g r:=gp.le
  have nl:0≤LogV r:=Real.log_nonneg ((one_le_inv₀ rp).mpr r1)
  have logfee:(LogV r/ν)^p*(g r)^(2*p)≤(c/ν)^p:=by
    rw [pow_mul,←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (div_nonneg nl vp.1.le) (sq_nonneg _))
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right logbill vp.1.le
  have meshpower:δ^(m+1)≤(g r)^(P+2*p+h):=by
    exact (pow_le_pow_left₀ dp.le mesh (m+1)).trans (by rw [←pow_mul];exact pow_le_pow_of_le_one gn g1 power)
  let a:=(LogV r/ν)^p
  let w:=∏i,Ascent.cost F (d i) r (v i)
  have an:0≤a:=pow_nonneg (div_nonneg nl vp.1.le) _
  have wn:0≤w:=prod_nonneg fun i _=>Ascent.cost_pos .. 
  refine (read δ dp (mesh.trans tiny) X sep ref v).trans ?_
  change A*δ^(m+1)*a*w≤A*(c/ν)^p*D*(g r)^P
  calc A*δ^(m+1)*a*w≤A*(g r)^(P+2*p+h)*a*w:=by gcongr
       _=A*(a*(g r)^(2*p))*(w*(g r)^h)*(g r)^P:=by simp only [pow_add];ring
       _≤A*(c/ν)^p*D*(g r)^P:=by gcongr

end YM.Integration.WilsonMeasuredPublicEntranceNamedTestGrid
end
