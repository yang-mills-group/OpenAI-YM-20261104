import YM.Integration.WilsonReflectedFourStations
import YM.Integration.WilsonRegisteredRectangleChannelClock

/-! Price a named physical cutoff primary at every finer date of the
same history. The first-connection tail sees only the true engineering
ratio and the original fee at the elected station. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedStationPrefix
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open GapsContact GapsContact.Seams GapsContact.Stamps Analysis Table Extraction Bid Spec Ascent Trace
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Next.Rank.Price
open PhysicalNext PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals
open WilsonReflectedOriginalVanes WilsonThermometerUnitFilingFourPool
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

private theorem columns (i:ℕ) :
    ((C).path.levels.params (i+1)).columns  ≤  (((C).S.block i).val:ℝ) := by
  have h:=WilsonRegisteredRectangleChannelClock.cost (C).path.levels i
  let a:=(C).path.levels.params (i+1)
  change 1+a.paths+a.width⁻¹+a.columns+a.clip.relaxation+a.supportExponent  ≤  _ at h
  change a.columns  ≤  _
  linarith only [h,a.paths_pos,inv_nonneg.mpr a.width_pos.le,a.price_pos,a.clip.radius_pos]

theorem quota {d j i N p:ℕ}(ref:(C).ref d ≤ j)(before:j ≤ i)(live:i ≤ N)(y:(C).label d):
    Next.UVStress.quota (C) d i N p y  ≤  ((C).S.a j/(C).S.a i)*Next.UVStress.quota (C) d j N p y:=by
  have cal:=R.makes.calibrated d N p ((ref.trans before).trans live)
  induction i,before using Nat.le_induction with
  | base => rw [div_self ((C).S.a_pos j).ne',one_mul]
  | succ i ji ih =>
    let L:ℝ:=((C).S.block i).val
    have pos:0<L:=by dsimp [L];exact_mod_cast ((C).S.block i).property
    have nn (u:ℕ):0 ≤ Next.UVStress.quota (C) d u N p y := by unfold Next.UVStress.quota Frame.coeffSize;positivity
    have back:=cal.back i (ref.trans ji) live (((C).factory d N p).terminal.symm y)
    change Next.UVStress.quota (C) d (i+1) N p y  ≤  ((C).path.levels.params (i+1)).columns*Next.UVStress.quota (C) d i N p y at back
    refine back.trans ((mul_le_mul_of_nonneg_right (columns R i) (nn i)).trans ?_)
    have prior:=ih (Nat.le_trans (Nat.le_succ i) live)
    apply (mul_le_mul_of_nonneg_left prior pos.le).trans_eq
    rw [(C).S.a_step]
    change L*(_ /(C).S.a i*_) = (_/((C).S.a i/L))*_
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv];ring

theorem original {h:Extraction.Order}{S:Table (C).book}{F:Final (C) h S}
    {l:Ultrafilter (ℕ×ℕ)}{r B:ℝ}{j m d:ℕ}{v:S.Field d}{Y:ℕ×ℕ→(C).label d}
    (source:Captured R F l r B j m d v Y){i N p:ℕ}(hi:j ≤ i)(live:i ≤ N)(nonbare:j<N):
    Next.UVStress.quota (C) d i N p (Y (N,p))  ≤  ((C).S.a j/(C).S.a i)*((C).S.a j^d*B*cost F d r v):=by
  exact (quota R source.reference hi live _).trans (mul_le_mul_of_nonneg_left (source.quota N p nonbare)
    (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le))

end YM.Integration.WilsonReflectedStationPrefix
end
