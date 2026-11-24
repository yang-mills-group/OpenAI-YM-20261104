import YM.Integration.WilsonMovingForkOpticalQuadrature
import YM.Integration.WilsonMovingForkTubeJets
import YM.Integration.WilsonCenteredReaderDomain
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolPublicCost
open Function Filter Finset Set Metric Extraction Table Spec PhysMS Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedGridTree WilsonSeparatedPhysicalRay WilsonSeparatedBranchStencil
open PhysicalNext.Repeat.Legato FVA2.Scale
open WilsonPositionHomogeneousFrame FVA2 FVA2.Register MS MS.Land RG17
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}(J:ℝ→tower S)(Z:WilsonPrescription G)
  {l:Ultrafilter (ℕ×ℕ)}{z:Trace.Terrace.Arch R.family}

theorem clearance {n:ℕ}{K:Set (Points n)}(compact:IsCompact K)(sep:K⊆conf n):
    ∃η:ℝ,0<η ∧ ∀x∈K,∀i j:Fin n,i≠j → η ≤ dist (x i) (x j):=by
  have edge (i j:Fin n) : ∃e:ℝ,0<e ∧ ∀x∈K,i≠j→e ≤ ‖x i-x j‖ :=by
    by_cases occupied : K.Nonempty
    · by_cases eq : i=j
      · exact ⟨1,zero_lt_one,fun _ _ h=>(h eq).elim⟩
      have cont : Continuous (fun x:Points n=>‖x i-x j‖) :=by fun_prop
      obtain ⟨x,hx,low⟩:=compact.exists_isMinOn occupied cont.continuousOn
      exact ⟨_,norm_pos_iff.mpr (sub_ne_zero.mpr ((sep hx).ne eq)),fun y hy _=>low hy⟩
    · exact ⟨1,zero_lt_one,fun x hx _=>(occupied ⟨x,hx⟩).elim⟩
  choose e pos bill using edge
  have near : ∀ᶠ η:ℝ in 𝓝 0,∀ i j,η<e i j := eventually_all.mpr fun i=>
    eventually_all.mpr fun j=>Iio_mem_nhds (pos i j)
  have small : ∀ᶠ η:ℝ in 𝓝[>] 0,∀i j,η<e i j :=near.filter_mono nhdsWithin_le_nhds
  obtain ⟨η,fit,hη⟩:=(small.and self_mem_nhdsWithin).exists
  exact ⟨η,hη,fun x hx i j ne=>by simpa only [dist_eq_norm] using (fit i j).le.trans (bill i j x hx ne)⟩

/-- The same physical continuum table prices every fixed combination of arms
at their own homogeneous reporting homes on a separated compact. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F J)
    (owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d){n:ℕ}(d:Fin n→ℕ)(h:ℕ)
    {K:Set (Points n)}(compact:IsCompact K)(sep:K⊆conf n):
    ∃B:ℝ,0 ≤ B ∧ ∃E:ℕ,∀ᶠr in trail,∀ρ:Fin n→ℝ,(∀i,r ≤ ρ i ∧ ρ i ≤ r/(wilson z r)^h) →
    ∀x∈K,∀v:(i:Fin n)→Free R.family (d i),
      ‖S.classMoment S d (r • x) (fun i=>WilsonPositionHomogeneousFrame.homogeneous F J Z (ρ i) (d i) (v i))‖*
        (wilson z r)^E ≤ B*(∏i,‖v i‖):=by
  obtain ⟨η,ep,cleared⟩:=clearance compact sep
  let g:=wilson z
  have hg:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨width,wp,ν,vp,A,an,p,tubes⟩:=WilsonMovingForkTubeJets.original F simple bliss d ep
  obtain ⟨D,dn,people⟩:=WilsonMovingForkPositionWage.original F J Z simple hg lead owed d h
  let L:=h*(∑i,(d i+1))
  let c:=G.slopeConstant⁻¹+1
  have cp:0<c:=by dsimp [c];positivity [Gauge.slopeConstant_pos simple]
  have bn:0 ≤ A*(c/ν)^p*D:=mul_nonneg (mul_nonneg an (pow_nonneg (div_nonneg cp.le vp.1.le) _)) dn
  refine ⟨_,bn,2*p+L,?_⟩
  have trailpos:=hg.running.eventually (ge_mem_nhds (by dsimp [c];linarith:G.slopeConstant⁻¹<c))
  filter_upwards [tubes,people,trailpos,hg.positive,self_mem_nhdsWithin,(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds]
    with r sample wages logbill gp (rp:0<r) (r1:r≤1)
  intro ρ span x hx v
  let fields(i:Fin n):=WilsonPositionHomogeneousFrame.homogeneous F J Z (ρ i) (d i) (v i)
  let w:=∏i,Ascent.cost F (d i) r (fields i)
  have wn:0 ≤ w:=prod_nonneg fun i _=>Ascent.cost_pos ..
  have nl:0 ≤ LogV r:=Real.log_nonneg ((one_le_inv₀ rp).mpr r1)
  have logfee:(LogV r/ν)^p*(g r)^(2*p) ≤ (c/ν)^p:=by
    rw [pow_mul,←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg (div_nonneg nl vp.1.le) (sq_nonneg _))
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right logbill vp.1.le
  have budget:w*(g r)^L ≤ D*(∏i,‖v i‖):=wages ρ span v
  have cash:‖S.classMoment S d (r • x) fields‖ ≤ A*(LogV r/ν)^p*w:=by
    simpa only [iteratedDeriv_zero,Pi.zero_apply,zero_smul,add_zero,Nat.factorial_zero,Nat.cast_one,one_mul,pow_zero,div_one]
      using sample x (cleared x hx) 0 (by simp) fields 0
  have nn:0 ≤ (g r)^(2*p+L):=pow_nonneg gp.le _
  have work:=mul_le_mul_of_nonneg_right cash nn
  calc
    _ ≤ (A*(LogV r/ν)^p*w)*(g r)^(2*p+L):=work
    _ = A*((LogV r/ν)^p*(g r)^(2*p))*(w*(g r)^L):=by rw [pow_add];ring
    _ ≤ A*(c/ν)^p*(D*(∏i,‖v i‖)):=by
      apply mul_le_mul (mul_le_mul_of_nonneg_left logfee an) budget (mul_nonneg wn (pow_nonneg gp.le _))
        (mul_nonneg an (pow_nonneg (div_nonneg cp.le vp.1.le) _))
    _ = _:=by ring

end YM.Integration.WilsonOriginalTwoFlatIRPoolPublicCost
end
