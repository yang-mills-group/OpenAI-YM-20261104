import YM.Integration.WilsonReceivedChronologicalFixedRoseClock
import YM.Integration.WilsonOriginalCensusFiledPhysicalEdge
import YM.Integration.WilsonReceivedChronologicalFixedRoseCutoffSalary

/-! Price a dated finite charge after restoring the genuine upper public socket wallet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseCashPower
open Function Filter Finset Lattice Wilson RG ActualRunAdmissionScales OriginalBareMarkedInvoice
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonReceivedChronologicalFixedPublicClock (roof)
open private relative from YM.Integration.WilsonMeasuredImpulseCalendar
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}
local notation "H" => R.family.path.levels.clock.hatBeta

private theorem wallet_nonneg (d:Fin n→ℕ)(s:Finset (Fin n))(money:ℝ)(nonneg:0 ≤ money):
    0≤wallet R d (fun _=>money) s:=by
  unfold WilsonReceivedCanonicalVersePortfolio.wallet
  exact prod_nonneg fun i _=>mul_nonneg (sum_nonneg fun j _=>WilsonReceivedCanonicalVersePortfolio.nonneg R d i j) nonneg

include simple in
theorem dated (d:Fin n→ℕ)(s:Finset (Fin n))(A pole p target:ℕ)(order:target+1+2*pole*n≤p)
    (B fare:ℝ)(bp:0≤B):
    ∀ᶠ v:ℕ in atTop,∀{K N per c:ℕ},0<v → v≤c → c≤N → K≤N →
      R.family.S.scale K-R.family.S.scale (v-1)≤(A:ℝ)*(1+Real.log (H v)) →
      wallet R d (fun _=>B*(H K)^pole) s*(fare*(regulatorRun R.family N per c)^p)
        ≤(regulatorRun R.family N per v)^target:=by
  let fixed:=wallet R d (fun _=>B*(roof (G:=G) A)^pole) s
  let rent:=|fare| * (2:ℝ)^p
  have rn:0≤rent:=mul_nonneg (abs_nonneg _) (by positivity)
  obtain ⟨floor,recover⟩:=WilsonReceivedChronologicalFixedRoseClock.original (n:=n) R simple
  filter_upwards [eventually_ge_atTop floor,WilsonOriginalOpticalCouplingBand.cold R simple (max 2 (fixed*rent))]
    with v early desk K N per c vp vc cn _kn span
  let g:=regulatorRun R.family N per v
  let atC:=regulatorRun R.family N per c
  have gp:0<g:=ActualRunKernelPackets.regulator_pos R N per v (vc.trans cn)
  have cp:0≤atC:=(ActualRunKernelPackets.regulator_pos R N per c cn).le
  have house:0≤wallet R d (fun _=>B*(H K)^pole) s:=wallet_nonneg R d s _
    (mul_nonneg bp (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed K).le) pole))
  have vn:v≤N:=vc.trans cn
  have paid:=desk N per vn
  have small:g≤1:=by
    have x:2≤g⁻¹:=(le_max_left ..).trans paid
    have one:1≤g⁻¹:=by linarith only [x]
    simpa [gp.ne'] using mul_le_mul_of_nonneg_right one gp.le
  have fc:atC≤2*g:=relative R.makes simple N per v c vc cn
  have month:fare*atC^p ≤ rent*(g^(target+1+2*pole*n)):=calc
    _ ≤ |fare| * atC^p:=mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg cp _)
    _ ≤ |fare| * (2*g)^p:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ cp fc _) (abs_nonneg _)
    _ = rent*g^p:=by simp only [rent,mul_pow];ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le small order) rn
  have succ:v-1+1=v:=Nat.sub_add_cancel vp
  have paidGain:=recover (m:=v-1) (top:=K) (N:=N) (per:=per) (by rwa [succ]) (by rwa [succ])
    A (by rwa [succ]) d s (target+1) pole B rent bp rn
  rw [succ] at paidGain
  have reserve:fixed*rent*g≤1:=(mul_le_mul_of_nonneg_right ((le_max_right ..).trans paid) gp.le).trans_eq
    (inv_mul_cancel₀ gp.ne')
  calc _ ≤ wallet R d (fun _=>B*(H K)^pole) s*(rent*g^(target+1+2*pole*n)):=
         mul_le_mul_of_nonneg_left month house
       _ ≤ fixed*(rent*g^(target+1)):=paidGain
       _ = (fixed*rent*g)*g^target:=by rw [pow_succ];ring
       _ ≤ 1*g^target:=mul_le_mul_of_nonneg_right reserve (pow_nonneg gp.le _)
       _ = _:=one_mul _

end YM.Integration.WilsonReceivedChronologicalFixedRoseCashPower
