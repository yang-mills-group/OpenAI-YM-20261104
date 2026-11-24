import YM.Integration.WilsonReflectedPublicBulbBerth
import YM.Integration.WilsonThermometerUnitFilingFourPoolClock

/-! The two originally named public stations, at the prescribed measuring
radius and the sharper weak radius, fit the same physical optical band. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicStationSpan
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open scoped Topology Classical
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "L" => R.family.path.levels
local notation "mesh" => R.family.S.a
local notation "β" => (L).clock.hatBeta

private theorem lower (simple:G.Simple) (bliss:Bliss F l z H):
    ∀ᶠ r in trail, ∀m,mesh m ≤ r → 1 ≤ 2*β m*(wilson z r)^2:=by
  let slope:=G.slopeConstant
  have sp:0<slope:=Gauge.slopeConstant_pos simple
  have half:slope⁻¹/2<slope⁻¹:=half_lt_self (inv_pos.mpr sp)
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  filter_upwards [self_mem_nhdsWithin,link.running.eventually (le_mem_nhds half)] with r rp wage
  change 0<r at rp
  change slope⁻¹/2 ≤ LogV r*(wilson z r)^2 at wage
  intro m atR
  have lg: LogV r ≤ R.family.S.scale m :=
    Real.log_le_log (inv_pos.mpr rp) (inv_anti₀ (R.family.S.a_pos m) atR)
  have cash:slope*R.family.S.scale m ≤ β m:=le_add_of_nonneg_left (L).clock.bar_pos.le
  have bound: slope*(LogV r*(wilson z r)^2) ≤ β m*(wilson z r)^2:=by
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left lg sp.le).trans cash) (sq_nonneg _)
  have fixed: slope*(slope⁻¹/2)=1/2:=by field_simp [sp.ne']
  linarith only [((mul_le_mul_of_nonneg_left wage sp.le).trans bound),fixed]

/-- Both stations of every pre-elected public pair fit one fixed inverse
temperature power. All coefficients and the preframe may vary with r. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(T:ℕ):
    ∀ᶠ r in trail, ∀ {D d k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {cap:d ≤ D}{W:Vane R.family k}{fits:D ≤ k}{U:Spin.change S d}
      (A:Pair F stock cap W fits U r), W.checked f H k → W.wheel.r=r →
      let m:=max stock.j W.k
      ∀b:Bool,mesh (station F A b)/mesh m ≤ (β m)^(2*T+3):=by
  obtain ⟨C,cp,invoice⟩:=WilsonThermometerUnitFilingFourPoolClock.invoice F simple bliss T
  let ex:=2*T+2
  obtain ⟨first,earn⟩:=eventually_atTop.mp (((pastTilt (L) simple).and
    ((hat_rate (L) simple).eventually_ge_atTop (max 1 (C*2^ex)))))
  let link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  filter_upwards [self_mem_nhdsWithin,(ge_mem_nhds (R.family.S.a_pos first)).filter_mono nhdsWithin_le_nhds,
    link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one),invoice,
    lower F simple bliss] with r rp early gp gu invBound pricing
  change 0<r at rp
  intro D d k stock cap W fits U A ok exactR m
  let s:=WilsonThermometerUnitFilingFourPoolShell.radius z T r
  let B:=dock s^T
  let g:=wilson z r
  have Wmesh:mesh W.k ≤ r:=(WilsonReflectedPublicBulbBerth.mesh R W ok).trans exactR.le
  have upcoming:first ≤ W.k:=by
    by_contra! nope
    exact (not_le_of_gt (R.family.S.strictAnti nope)) (Wmesh.trans early)
  have wm:W.k ≤ m:=le_max_right .. 
  have fee:=earn m (upcoming.trans wm)
  have bp:1 ≤ β m:=(le_max_left ..).trans fee.2
  have wp:1 ≤ 2*β m:=by linarith
  have fine:1 ≤ 2*β m*g^2:=pricing m ((R.family.S.strictAnti.antitone wm).trans Wmesh)
  have power (q:ℕ):1 ≤ (2*β m)^q*(g^2)^q:=by simpa only [←mul_pow] using (one_le_pow₀ (n:=q) fine)
  have posB:0 ≤ B:=pow_nonneg invBound.1.le _
  have Bbill: B ≤ C*(2*β m)^T:=by
    calc
      B ≤ B*((2*β m)^T*(g^2)^T):=le_mul_of_one_le_right posB (power T)
      _ = (dock s^T*(g^(2*T)))*(2*β m)^T:=by rw [pow_mul];ring
      _ ≤ C*(2*β m)^T:=mul_le_mul_of_nonneg_right invBound.2 (pow_nonneg (zero_le_one.trans wp) _)
  have μ:mag (L) W.b W.k ≤ β m:=((tiltP (C:=R.family) _ ok.high.2).trans (earn W.k upcoming).1).trans
    (WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos simple).le wm)
  let room:=stock.department d cap
  let slot:=room.print (0:S.Field d)
  have atj:slot.j=stock.j:=(room.dated _).1
  have low:s ≤ B*mesh stock.j:=atj ▸ slot.breadth.le
  have top:mesh stock.j ≤ s*B:=by
    rw [←atj];exact (R.family.S.strictAnti.antitone slot.fore).trans slot.front.le
  have sr:s ≤ r := mul_le_of_le_one_right rp.le (pow_le_one₀ gp.le gu)
  have exactW:r=mesh W.k*mag (L) W.b W.k:=exactR.symm
  have major:B*(2*β m)^(T+2) ≤ (β m)^(2*T+3):=by
    calc
      _ ≤ (C*(2*β m)^T)*(2*β m)^(T+2):=mul_le_mul_of_nonneg_right Bbill (pow_nonneg (by linarith) _)
      _ = (C*2^ex)*(β m)^ex:=by
        rw [mul_assoc,←pow_add,show T+(T+2)=ex by dsimp [ex];omega,mul_pow,mul_assoc]
      _ ≤ (β m)*(β m)^ex:=mul_le_mul_of_nonneg_right ((le_max_right ..).trans fee.2) (pow_nonneg (by linarith) _)
      _ = _:=by change _ = (β m)^(ex+1);rw [pow_succ];ring
  have forward:mesh stock.j ≤ mesh W.k*(β m)^(2*T+3):=by
    calc
      _ ≤ s*B:=top
      _ ≤ (mesh W.k*β m)*B:=mul_le_mul_of_nonneg_right (sr.trans (exactW.trans_le
        (mul_le_mul_of_nonneg_left μ (R.family.S.a_pos _).le))) posB
      _ ≤ mesh W.k*(B*(2*β m)^(T+2)):=by
        rw [mul_assoc,mul_comm (β m) B]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((by linarith : β m ≤ 2*β m).trans
          (le_self_pow₀ (n:=T+2) wp (by omega))) posB) (R.family.S.a_pos _).le
      _ ≤ _:=mul_le_mul_of_nonneg_left major (R.family.S.a_pos _).le
  have reverse:mesh W.k ≤ mesh stock.j*(β m)^(2*T+3):=by
    have price:r ≤ s*(2*β m)^(T+2):=by
      refine (le_mul_of_one_le_right rp.le (power (T+2))).trans_eq ?_
      dsimp [s,WilsonThermometerUnitFilingFourPoolShell.radius]
      rw [←pow_mul,show 2*(T+2)=2*T+4 by omega];ring
    calc
      _ ≤ r:=Wmesh
      _ ≤ s*(2*β m)^(T+2):=price
      _ ≤ (B*mesh stock.j)*(2*β m)^(T+2):=mul_le_mul_of_nonneg_right low (pow_nonneg (by linarith) _)
      _ = mesh stock.j*(B*(2*β m)^(T+2)):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left major (R.family.S.a_pos _).le
  intro b
  rw [div_le_iff₀ (R.family.S.a_pos m),mul_comm]
  have own (n:ℕ):mesh n ≤ mesh n*(β m)^(2*T+3):=le_mul_of_one_le_right (R.family.S.a_pos n).le (one_le_pow₀ bp)
  rcases le_total stock.j W.k with left|right
  · have eq:m=W.k:=max_eq_right left
    cases b
    · simpa only [station,Bool.false_eq_true,reduceIte,←eq] using forward
    · simpa only [station,↓reduceIte,←eq] using own W.k
  · have eq:m=stock.j:=max_eq_left right
    cases b
    · simpa only [station,Bool.false_eq_true,reduceIte,←eq] using own stock.j
    · simpa only [station,↓reduceIte,←eq] using reverse

end YM.Integration.WilsonReflectedPublicStationSpan
end
