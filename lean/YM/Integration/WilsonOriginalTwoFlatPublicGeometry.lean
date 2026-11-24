import YM.Integration.WilsonReflectedPublicStationSpan
import YM.Integration.WilsonReflectedOpticalWidth

/-! At the actual common optical berth the entire finite separated physical
shape fits a reflection chamber and clears the native interaction radius. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicGeometry
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open scoped Topology Classical

open WilsonInvariantActionPosition WilsonReflectedOriginalPrefixTariff
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

theorem clearance (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    {η:ℝ}(ep:0<η):∀ᶠ m:ℕ in atTop,let j:=berth R 5 m
    2*a j*((((P).budget j).B:ℝ)^2) ≤ η*a m:=by
  obtain ⟨M,Z,mp,_,widths⟩:=WilsonReflectedOpticalWidth.original R simple slow 0 5 (η:=1) zero_lt_one
  let W:ℝ:=2*(M^2+2)^2
  filter_upwards [widths,WilsonAddressedCollarWindow.original R simple slow 5 (η:=1) zero_lt_one,
    (hat_rate (P) simple).eventually_ge_atTop (W/η)] with m offered edge big
  let j:=berth R 5 m
  have hm:1≤β m:=((P).fits.delayed m).le
  have hj:1≤β j:=((P).fits.delayed j).le
  have mt:0≤M*β m:=mul_nonneg mp.le (zero_le_one.trans hm)
  have lg:Real.log (β j)≤M*β m:=by
    obtain ⟨first,_⟩:=offered
    dsimp only [WilsonReflectedOriginalPrefixTariff.width] at first
    exact le_trans (by linarith only [abs_nonneg G.slopeConstant]) first
  have side:(((P).budget j).B:ℝ)≤(M^2+2)*(β m)^2:=by
    change (⌈(Real.log (β j))^2⌉₊:ℝ)≤_
    have ht:=(Nat.ceil_lt_add_one (sq_nonneg (Real.log (β j)))).le
    have hh:=pow_le_pow_left₀ (Real.log_nonneg hj) lg 2
    nlinarith only [ht,hh,one_le_pow₀ (n:=2) hm]
  have p:(0:ℝ)≤((P).budget j).B:=by positivity
  have fee: W ≤ η*β m:=by simpa [mul_comm] using (div_le_iff₀ ep).mp big
  have paid:2*((((P).budget j).B:ℝ)^2)≤η*(β m)^5:=by
    calc
      _ ≤ 2*((M^2+2)*(β m)^2)^2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p side _) zero_le_two
      _ = W*(β m)^4:=by dsimp [W];ring
      _ ≤ (η*β m)*(β m)^4:=mul_le_mul_of_nonneg_right fee (pow_nonneg (zero_le_one.trans hm) _)
      _ = _:=by ring
  have gain:(β m)^5*a j≤a m:=(le_div_iff₀ (R.family.S.a_pos j)).mp edge.2.1
  calc
    _ = (2*((((P).budget j).B:ℝ)^2))*a j:=by ring
    _ ≤ (η*(β m)^5)*a j:=mul_le_mul_of_nonneg_right paid (R.family.S.a_pos _).le
    _ ≤ _:=by rw [mul_assoc];exact mul_le_mul_of_nonneg_left gain ep.le

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (T floor u:ℕ){M η:ℝ}(one:1≤M)(ep:0<η):
    ∀ᶠ r in trail,∀{D d k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {cap:d≤D}{W:Vane R.family k}{fits:D≤k}{U:Spin.change S d}
      (A:Pair F stock cap W fits U r),W.checked f H k → W.wheel.r=r →
      let m:=max stock.j W.k
      let j:=berth R 5 m
      floor≤j ∧ 0<8*M*r ∧ 8*M*r≤a (u+3) ∧ a j<8*M*r ∧ 8*M*r≤(β j)^(2*T+11)*a j ∧
      2*a j*((((P).budget j).B:ℝ)^2)≤η*r ∧ ∀b:Bool,station F A b ≤ j:=by
  obtain ⟨first,all⟩:=eventually_atTop.mp (((clearance (R:=R) simple slow ep).and
    (WilsonAddressedCollarWindow.original R simple slow 5 (η:=1) zero_lt_one)).and
    ((pastTilt (P) simple).and ((hat_rate (P) simple).eventually_ge_atTop (8*M))))
  have Mpos:0<8*M:=by linarith
  filter_upwards [self_mem_nhdsWithin, (ge_mem_nhds (R.family.S.a_pos (max floor first))).filter_mono nhdsWithin_le_nhds,
    (ge_mem_nhds (div_pos (R.family.S.a_pos (u+3)) Mpos)).filter_mono nhdsWithin_le_nhds,
    WilsonReflectedPublicStationSpan.original F simple bliss T] with r rp fit small fees
  change 0<r at rp
  intro D d k stock cap W fits U A checked agreed m j
  have Wm:W.k≤ m:=le_max_right .. 
  have Wr:a W.k≤r:=(WilsonReflectedPublicBulbBerth.mesh R W checked).trans agreed.le
  have past:max floor first≤W.k:=by
    by_contra! before
    exact (not_le_of_gt (R.family.S.strictAnti before)) (Wr.trans fit)
  have allW:=all W.k ((le_max_right ..).trans past)
  have allM:=all m (((le_max_right ..).trans past).trans Wm)
  have edge:=allM.1.2
  have beta:0<β m:=zero_lt_one.trans ((P).fits.delayed m)
  have monotone:=WilsonStartup.Timing.hat_mono (P) (Gauge.slopeConstant_pos simple).le
  have WtoF:=monotone (show m≤j from edge.1.le)
  have Wsize:a W.k≤(β m)^(2*T+3)*a m:=(div_le_iff₀ (R.family.S.a_pos m)).mp
    (by simpa only [station,if_true] using fees A checked agreed true)
  have amp:mag (P) W.b W.k≤β m:=((tiltP (C:=R.family) _ checked.high.2).trans allW.2.1).trans (monotone Wm)
  have fine:a m≤(β m)^6*a j:=(div_le_iff₀ (R.family.S.a_pos j)).mp (by
    simpa [Real.rpow_one,show (6:ℕ)=5+1 by decide,pow_succ] using edge.2.2)
  have clock:8*M*r≤(β j)^(2*T+11)*a j:=by
    have exactW:r=a W.k*mag (P) W.b W.k:=agreed.symm
    have mag0:0 ≤ mag (P) W.b W.k:=((mul_pos_iff_of_pos_left (R.family.S.a_pos _)).mp (exactW ▸ rp)).le
    have hi:=Wsize.trans (mul_le_mul_of_nonneg_left fine (pow_nonneg beta.le _))
    have row:=mul_le_mul hi amp mag0 ((R.family.S.a_pos _).le.trans hi)
    calc
      _ ≤ (β m)*(((β m)^(2*T+3)*((β m)^6*a j))*β m):=by
        rw [exactW];exact mul_le_mul allM.2.2 row (mul_nonneg (R.family.S.a_pos _).le mag0) beta.le
      _ = (β m)^(2*T+11)*a j:=by rw [show 2*T+11=(2*T+3)+8 by omega,pow_add];ring
      _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ beta.le WtoF _) (R.family.S.a_pos _).le
  have mr:a m≤r:=(R.family.S.strictAnti.antitone Wm).trans Wr
  have clearance:=allM.1.1
  refine ⟨(((le_max_left ..).trans past).trans Wm).trans edge.1.le,mul_pos Mpos rp,
    by simpa [mul_comm] using (le_div_iff₀ Mpos).mp small,?_,clock,clearance.trans (mul_le_mul_of_nonneg_left mr ep.le),?_⟩
  · apply (R.family.S.strictAnti edge.1).trans_le (mr.trans ?_)
    exact le_mul_of_one_le_left rp.le (by linarith)
  · intro b
    cases b <;> simp only [station,Bool.false_eq_true,if_false,if_true]
    · exact (le_max_left ..).trans edge.1.le
    · exact Wm.trans edge.1.le

end YM.Integration.WilsonOriginalTwoFlatPublicGeometry
end
