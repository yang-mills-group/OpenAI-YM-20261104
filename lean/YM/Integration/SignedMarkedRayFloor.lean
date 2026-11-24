import YM.Integration.ActualNormalizedRayJets
import YM.Integration.NativePaidPacketColors
import YM.Comparison.RG02.Adjacent.Sale

/-! Exact field degree of every Laurent coefficient of the actual charged nonlinear Wilson packet. The whole-bank minimal clearing includes the endpoint z = -powerCap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedMarkedRayFloor
open Function Filter Finset Lattice Wilson RG Marker Multi Exterior Precision LocalComparison
open Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Valence NativePaidPacketColors
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {n : Side} {S : Census V} {D : V → ComparisonDensity.Address.Orbit}
variable (P : MarkedPackets D G n S)
local notation "E₀" => fieldDir G n 1

def numerator (x : TestSpace D) (s : S.Mode) (u : ℝ×E₀) : ℂ := if s=S.quiet then 0 else
  ∑z∈powers P, u.1^((P.powerCap:ℤ)+z).toNat • NativePaidPacketSeries.value P s z x (represent u.2)

variable {P} {p : BudgetPoint} {ad : V → Support n} {reg : Comparison.Density.Testing.Region (fun i=>(D i).Mood) n} {weights : V → ℝ} {g₀ width budget : ℝ} {offset slope : ℕ}
    (H:P.Paid p ad reg weights g₀ width budget offset slope) (hg₀:g₀≠0)

omit [Fintype V] in
include H hg₀ in
/-- The authentic numerator vanishes through the full minimal common clearing. Its endpoint exponent is allowed to be zero, by the actual field-valence floor. -/
theorem grade (x : TestSpace D) (s : S.Mode) : GradeAt P.powerCap (numerator P x s) := by
  by_cases hs:s=S.quiet
  · have hz : numerator P x s=fun _=>0 := funext fun _=>if_pos hs
    rw [hz]
    exact ⟨contDiffAt_const,fun i _=>by simp⟩
  have hsumm : numerator P x s=fun u=>∑z∈powers P,u.1^((P.powerCap:ℤ)+z).toNat •
      NativePaidPacketSeries.value P s z x (represent u.2) := funext fun _=>if_neg hs
  rw [hsumm]
  apply GradeAt.list_sum
  intro z hz
  have hp:=GradeAt.shifts (fun u:ℝ×E₀=>u.1) contDiffAt_fst rfl ((P.powerCap:ℤ)+z).toNat
  have hq:=(NativePaidPacketSeries.value_grade H hg₀ s hs z x).coarse (g:=fun u:ℝ×E₀=>u.2) contDiffAt_snd rfl
  apply (hp.scale hq).lower
  have lo : -(P.powerCap:ℤ)≤z := (mem_Icc.mp hz).1
  omega

include H hg₀ in
private theorem empty (x : TestSpace D) (t : ℝ) (U : Config G n) : (P.read x t U).part S.quiet=0 := by
  rw [MarkedPackets.read,Poly.share (NativePaidPacketColors.read_summable H hg₀ x t U)]
  have hzero (i:ℕ) : (Poly.send (P.mode i) (P.term x t U i)).part S.quiet=0 := by
    cases hi:P.packet i with
    | none=>simp [MarkedPackets.term,hi]
    | some T=>simp only [Poly.part_send,if_neg (Ne.symm (P.marked i T hi))]
  simp only [hzero,tsum_zero]

include H hg₀ in
/-- On the punctured physical line this is precisely the measured signed bank at the same coupling and arbitrary original field. -/
theorem paid (x : TestSpace D) (s : S.Mode) (t : ℝ) (ht:t≠0) (A : E₀) :
    t^P.powerCap • (P.read x t (represent A)).part s=numerator P x s (t,A) := by
  by_cases hs:s=S.quiet
  · subst s;simp [numerator,empty H hg₀]
  rw [numerator,if_neg hs,NativePaidPacketColors.read_mode_sum H hg₀ s hs,smul_sum]
  apply sum_congr rfl;intro z hz
  have lo : -(P.powerCap:ℤ)≤z := (mem_Icc.mp hz).1
  have hpow : (((P.powerCap:ℤ)+z).toNat:ℤ)=(P.powerCap:ℤ)+z := by omega
  have hT : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht
  have he : (t:ℂ)^P.powerCap*(t:ℂ)^z=(t:ℂ)^((P.powerCap:ℤ)+z).toNat := by
    calc _=(t:ℂ)^((P.powerCap:ℤ)+z):=by simpa only [zpow_natCast] using (zpow_add₀ hT (P.powerCap:ℤ) z).symm
         _=(t:ℂ)^((((P.powerCap:ℤ)+z).toNat:ℤ)):=congrArg (fun e:ℤ=>(t:ℂ)^e) hpow.symm
         _=_:=zpow_natCast ..
  simpa only [Complex.real_smul,Complex.ofReal_pow,mul_assoc] using congrArg (fun v:ℂ=>v*NativePaidPacketSeries.value P s z x (represent A)) he

include H hg₀ in
/-- Exactly the original field polynomial of every finite selected charged-ray coefficient. A continuous extension on the coupling line is sufficient, including the full quiet component. -/
theorem ray (x : TestSpace D) (s : S.Mode) (E : ℝ → E₀ → Poly S)
    (hE:∀t:ℝ,t≠0→∀A:E₀,E t A=P.read x t (represent (t • A)))
    (hc:∀A:E₀,ContinuousAt (fun t=>E t A) 0) (k:ℕ) (B:E₀) :
    Assembly.jet (fun t=>(E t B).part s) k 1=Assembly.jet (numerator P x s) (P.powerCap+k) (1,B) := by
  let π : Poly S →L[ℝ] ℂ := ContinuousLinearMap.proj s
  apply ActualNormalizedRayJets.joint_coefficient (grade H hg₀ x s) B (π.continuous.continuousAt.comp (hc B))
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht₀:t≠0:=by simpa using ht
  change (E t B).part s=_
  rw [hE t ht₀ B,←paid H hg₀ x s t ht₀ (t • B),smul_smul,inv_mul_cancel₀ (pow_ne_zero _ ht₀),one_smul]

omit [Fintype V] in
include H hg₀ in
theorem joint (x:TestSpace D) (s:S.Mode) (k:ℕ) : Level (P.powerCap+k:ℕ) (Assembly.jet (numerator P x s) (P.powerCap+k)) :=
  Adjacent.levelJet (grade H hg₀ x s).smooth _
end YM.Integration.SignedMarkedRayFloor
