import YM.Integration.WilsonAddressedPublicCardBooks
import YM.Integration.WilsonMovingForkReporterClock
import YM.Integration.WilsonOriginalTwoFlatPublicGeometry

/-! Common subpower control of every purchased width before the optical reporting date. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonAddressedPublicOpticalClock
open Function Filter Set Finset Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open PhysicalNext.Repeat.Legato Lattice Wilson RG Source Extraction Next.Rank
open Next.Rank.Station Trace.Terrace WilsonReflectedOriginalPrefixTariff WilsonInvariantActionPosition
open MergeProof.East Next.UVStress WilsonMeasuredPublicBank WilsonPositionProgramPublicStations
open WilsonOriginalTwoFlatPublicBooks (Book)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta
local notation "M" => (A).clock.monitor
local notation "a" => R.family.S.a

theorem monitor (simple:G.Simple){η:ℝ}(ep:0<η):∃B:ℝ,1≤B ∧ ∀{j i:ℕ},i≤j → (M i)^6≤B*((β j)^η):=by
  have deep:∀ᶠ i:ℕ in atTop,(M i)^6 ≤ (β i)^η:=by
    filter_upwards [(hat_rate (A) simple).eventually (Vac.Numbers.cost 6 η ep)] with i bound
    simpa [Vac.Numbers.P,Calendar.monitor] using bound
  have monotone:=WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le
  obtain ⟨n,late⟩:=eventually_atTop.mp deep
  let B:=1+∑i∈range n,(M i)^6
  have nn:0 ≤ ∑i∈range n,(M i)^6:=sum_nonneg (fun _ _=>pow_nonneg (Real.exp_pos _).le 6)
  have one:1 ≤ B:=by dsimp only [B];linarith only [nn]
  refine ⟨B,one,?_⟩
  intro j i ij
  have bp:1 ≤ β j:=((A).fits.delayed j).le
  have pos:0 ≤ (β j)^η:=Real.rpow_nonneg (zero_le_one.trans bp) _
  by_cases mature : n ≤ i
  · exact (late i mature).trans ((Real.rpow_le_rpow (zero_le_one.trans ((A).fits.delayed i).le)
      (monotone ij) ep.le).trans (le_mul_of_one_le_left pos one))
  · have inside:i∈range n:=mem_range.mpr (Nat.lt_of_not_ge mature)
    have whole: (M i)^6 ≤ ∑k∈range n,(M k)^6:=single_le_sum (f:=fun j=>(M j)^6) (fun j _=>by positivity) inside
    exact (whole.trans (by dsimp only [B];linarith : _ ≤ B)).trans
      (le_mul_of_one_le_right (zero_le_one.trans one) (Real.one_le_rpow bp ep.le))

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (T floor:ℕ){η:ℝ}(ep:0<η):
    ∃E:ℝ,1≤E ∧ ∀ᶠ r in trail,∀{D:ℕ}(B:Book F (l:=l) H z D T r),
    let j:=berth R 5 (max B.stock.j B.W.k)
    floor≤j ∧ B.stock.j≤j ∧ B.W.k≤j ∧ ∀{i:ℕ},i≤j →
      (M i)^6*((wilson z r)^2)^η ≤ E:=by
  have here:=WilsonOriginalTwoFlatPublicGeometry.original F simple bliss slow T floor 0 (η:=1) (show (1:ℝ)≤1 by rfl) one_pos
  obtain ⟨C,cp,scale⟩:=WilsonMovingForkReporterClock.original F simple bliss (2*T+11)
  obtain ⟨B₀,bp,budget⟩:=monitor (R:=R) simple ep
  refine ⟨max 1 (B₀*C^η),le_max_left ..,?_⟩
  filter_upwards [here,scale,self_mem_nhdsWithin] with r placed priced rp D B j
  have pos:0<r:=rp
  let d:Fin (D+1):=⟨0,by omega⟩
  have purchased:=placed (B.rows d) B.checked B.active
  have home:B.W.k≤j:=purchased.2.2.2.2.2.2 true
  have stock:B.stock.j≤j:=purchased.2.2.2.2.2.2 false
  have mesh:a j≤r:=(R.family.S.strictAnti.antitone home).trans ((WilsonReflectedPublicBulbBerth.mesh R _ B.checked).trans B.active.le)
  have gap:8*1*r ≤ (β j)^(2*T+11)*a j:=purchased.2.2.2.2.1
  have invoice:=priced j mesh (show r≤(β j)^(2*T+11)*a j by linarith only [pos,gap])
  have hp:0≤β j:=zero_le_one.trans ((A).fits.delayed j).le
  have gp:0≤(wilson z r)^2:=sq_nonneg _
  have combined:(β j)^η*((wilson z r)^2)^η ≤ C^η:=by
    rw [←Real.mul_rpow hp gp]
    exact Real.rpow_le_rpow (mul_nonneg hp gp) invoice ep.le
  refine ⟨purchased.1,stock,home,?_⟩
  intro i dates
  calc
    _ ≤ (B₀*(β j)^η)*((wilson z r)^2)^η:=mul_le_mul_of_nonneg_right (budget dates) (Real.rpow_nonneg gp η)
    _ ≤ B₀*C^η:=by rw [mul_assoc];exact mul_le_mul_of_nonneg_left combined (zero_le_one.trans bp)
    _ ≤ _:=(le_max_right ..)

end YM.Integration.WilsonAddressedPublicOpticalClock
end
