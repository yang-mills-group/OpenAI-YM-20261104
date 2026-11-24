import YM.Integration.WilsonThermometerWeakRunningCoordinates
import YM.OPE.Splitting.Legacy

/-! The complete running field in a coherent finite ordinary basis.  Its
coordinate expenditure is measured before choosing numerical fields or their
directions, on the joint Wilson cutoff used by the logarithmic tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakRunningRoster
open Finset Filter Set Spec Table Extraction Trace Trace.Pilot Trace.Terrace
open GapsContact GapsContact.Ascent GapsContact.Seams Frontier6 OPE OPE.Log
open PhysicalNext.Repeat.Legato Next.UVStress
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  (P:Prescription F.sector.derivatives)

def rent (d:ℕ)(r:ℝ)(v:S.Field d):ℝ :=
  ∑ a:↥(bands F.sector.derivatives d), ‖P.test a.1 d v‖/r^a.1.fst

theorem original {simple:G.Simple}{A:EveryPhase.Almanac F}(H:Roll.{u} F simple A)
    (agency:∀𝓛:Ultrafilter (ℕ×ℕ),(𝓛:Filter _)≤f.fuse→MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (hp:Prescription.Coherent P)(d:ℕ):
    ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠr in trail,∀v:S.Field d,
      rent F P d r v≤C*dock r^m*cost F d r v:=by
  let T:=↥(bands F.sector.derivatives d)
  have entry (a:T) : ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠ r in trail,∀v:S.Field d,
      ‖P.test a.1 d v‖≤C*dock r^m*r^a.1.fst*cost F d r v:=by
    exact WilsonThermometerWeakRunningCoordinates.original F H agency (P.test a.1 d)
      ((full_bands ..).mp a.2) (fun e he x=>by
        rw [Prescription.affinity F.room.kernel.laws.toSymmetric F.phase.transport.injection P,
          Prescription.highVan F.room.kernel.laws.toSymmetric F.phase.transport.injection hp a.1 he])
  choose C m nonneg paid using entry
  refine ⟨∑a,C a,∑a,m a,sum_nonneg (fun i _=>nonneg i),?_⟩
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_all.mpr paid,small,self_mem_nhdsWithin] with r hr h1 h0
  intro v
  have lev:1≤dock r:=dock_valid r ⟨h0,h1⟩
  unfold rent
  rw [sum_mul,sum_mul]
  apply sum_le_sum
  intro a _
  have size:m a≤∑i,m i:=single_le_sum (fun i _=>Nat.zero_le (m i)) (mem_univ a)
  calc
    _ ≤ C a*dock r^(m a)*cost F d r v := by
      apply (div_le_iff₀ (pow_pos h0 a.1.fst)).mpr
      simpa only [mul_assoc,mul_comm (r^a.1.fst)] using hr a v
    _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ lev size) (nonneg a)) (Real.sqrt_nonneg _)

end YM.Integration.WilsonThermometerWeakRunningRoster
end
