import YM.Integration.WilsonMeasuredSignedActionPosition
import YM.Integration.WilsonMovingForkReporterRestriction

/-! A nominated, already issued book is used at each reporter. Its true
two-cutoff weak arms at the unit and at the action determine the sign of
the inverse on the original physical field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionBooked
open Function Filter Set Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open WilsonMeasuredSignedActionOriginalTables WilsonThermometerUnitFilingFourSquare
open PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
local notation "C" => R.family

private theorem unit {D T:ℕ}{r:ℝ}(B:Book F (l:=l) H Z D T r)(i:Fin (D+1))
    (bliss:Bliss F l Z H): B.V i ((Bel (C).book).unit i)=S.unit i:=by
  let v:=B.V i ((Bel (C).book).unit i)
  let A:=(B.rows i).arm true v
  let j:Fin (B.k+1):=⟨i.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.isLt).trans B.fits)⟩
  have same:∀z,A.source z=B.W.wheel.atCut z j ((Bel (C).book).unit i):=by
    intro z
    simpa only [A,v,LinearEquiv.symm_apply_apply] using (B.rows i).weak v z
  have reads:A.source =ᶠ[(l:Filter (ℕ×ℕ))] fun _=>(C).book.scalar i:=by
    filter_upwards [(large_mesh f (B.W.k+1)).filter_mono bliss.lies] with z live
    rw [same z]
    change Next.Rank.East.ladd _ _ _ _ _ _ _ (Further.CorrectedLift.ladder _ _ _) = _
    rw [Further.CorrectedLift.ladder_unit]
    exact Next.Rank.East.pure_start R.makes (B.checked.early j) (Nat.le_of_lt live) _
      _ (((B.checked.rate _ _ live).1 j).1)
  exact A.represents.symm.trans (congrArg (S.project i)
    (tendsto_nhds_unique_of_eventuallyEq A.approaches tendsto_const_nhds reads))

theorem original (simple:G.Simple)(bliss:Bliss F l Z H)
    {J:ℝ→PhysMS.tower S}{P:ℝ→Spin.change S 4}{δ g:ℝ→ℝ}
    (frame:∀ᶠ r in trail,J r 4=P r)(cal:TendC F P δ)(heat:Coupling G g)
    (X:Zoom){D T:ℕ→ℕ}(B:∀m,Book F (l:=l) H Z (D m) (T m) (X.r m))
    (roof:∀m,m≤(B m).k)(stages:Tendsto (fun m=>(B m).W.k) atTop atTop):
    ∀ᶠ m:ℕ in atTop,∀h:4 ≤ D m,
      let i:Fin (D m+1):=⟨4,Nat.lt_succ_of_le h⟩
      ∃(s:ℝ)(c:ℂ),0<s ∧ ((B m).V i).symm (J (X.r m) 4 (stepField C))=
        s • stepField C + c • (Bel (C).book).unit 4:=by
  let V:=fun m=>WilsonMovingForkReporterRestriction.vane (roof m) (B m).W
  have checked:∀m,(V m).checked f H m:=fun m=>
    WilsonMovingForkReporterRestriction.checked (roof m) (B m).W (B m).checked
  have onV:=named F simple bliss X V checked (fun m=>(B m).active) stages
  have small:Tendsto X.r atTop trail:=tendsto_nhdsWithin_iff.mpr ⟨X.limits,Eventually.of_forall X.positive⟩
  filter_upwards [onV,small.eventually (WilsonMeasuredSignedActionPosition.positioned F simple frame cal heat),
    eventually_ge_atTop 4] with m received old hm
  intro h i
  let v:=(B m).V i (stepField C)
  let A:=((B m).rows i).arm true v
  have paid:=received hm v A (fun z=>by
    rcases z with ⟨N,per⟩
    dsimp only [A,V]
    rw [WilsonMovingForkReporterRestriction.row]
    simpa only [i,v,LinearEquiv.symm_apply_apply,WilsonMovingForkReporterRestriction.slot] using ((B m).rows i).weak v (N,per))
  exact WilsonMeasuredSignedActionPosition.sameRay F (unit F (B m) i bliss) paid old

end YM.Integration.WilsonMeasuredSignedActionBooked
