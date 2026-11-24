import YM.Integration.WilsonReceivedChronologicalFixedRoseCashPower
import YM.Integration.WilsonReceivedChronologicalFixedRoseFittedBank

/-! Restore the fitted physical wallet on the five dated contributions to a finite roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterSalary
open Filter Finset Lattice Wilson RG Marker
open OriginalBareMarkedInvoice Pert.Asymptotics
open WilsonReceivedCanonicalVersePortfolio (wallet)
open PhysicalNext.Repeat.Legato ActualRunAdmissionScales
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}
local notation "H" => R.family.path.levels.clock.hatBeta

include simple in
theorem original (d:Fin n→ℕ)(A pole target:ℕ)(B:ℝ)(bp:0≤B)
    (exponent:Fin 5→ℕ)(adequate:∀i,target+2+2*pole*n ≤ exponent i)
    (fare:(Stock.census (Fin n)).Mode→Fin 5→ℝ):
    ∀ᶠ v:ℕ in atTop,∀s:(Stock.census (Fin n)).Mode,∀{K N per:ℕ},0<v→K≤N→
    R.family.S.scale K-R.family.S.scale (v-1)≤(A:ℝ)*(1+Real.log (H v))→
    ∀dates:Fin 5→ℕ,(∀i,v≤dates i ∧ dates i≤N)→∀T:Finset (Fin 5),
      (wallet R d (fun _=>B) s.val*(H K)^(pole*s.val.card))*
        (∑i∈T,fare s i*(regulatorRun R.family N per (dates i))^(exponent i))≤
          (regulatorRun R.family N per v)^target:=by
  have published (s:(Stock.census (Fin n)).Mode)(i:Fin 5):=
    WilsonReceivedChronologicalFixedRoseCashPower.dated R simple d s.val A pole (exponent i) (target+1)
      (adequate i) B (fare s i) bp
  filter_upwards [eventually_all.mpr (fun s=>eventually_all.mpr (published s)),
    WilsonOriginalOpticalCouplingBand.cold R simple 5] with v funded cold
  intro s K N per pos kn span dates live T
  let g:=regulatorRun R.family N per v
  have vn:v≤N:=(live 0).1.trans (live 0).2
  have gp:0<g:=ActualRunKernelPackets.regulator_pos R N per v vn
  have small:5*g≤1:=(mul_le_mul_of_nonneg_right (cold N per vn) gp.le).trans_eq (inv_mul_cancel₀ gp.ne')
  have count:T.card≤5:=by simpa using T.card_le_univ
  rw [←WilsonReceivedChronologicalFixedRoseFittedBank.factor,mul_sum]
  calc _ ≤ ∑_i∈T, g^(target+1):=Finset.sum_le_sum fun i _=>
            funded s i pos (live i).1 (live i).2 kn span
       _ = (T.card:ℝ)*g^(target+1):=by simp
       _ ≤ 5*g^(target+1):=mul_le_mul_of_nonneg_right (by exact_mod_cast count) (pow_nonneg gp.le _)
       _ = (5*g)*g^target:=by rw [pow_succ];ring
       _ ≤ _:=mul_le_of_le_one_left (pow_nonneg gp.le _) small
end YM.Integration.WilsonReceivedChronologicalRosterSalary
end
