import YM.Integration.WilsonMacroscopicRichCroppedDeposit
import YM.Integration.WilsonMacroscopicRichCaptureWrap

/-! Select the physical aperture for the positive Hermite probe on an original funded terminal account. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichAperture
open Filter Function Set Lattice Wilson RG OPE OPE.Orbits Source Labels Spec PhysMS
open RG16 RG16.Literal Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open RGComparison.Core16 Analysis Next.Foundations Push.Local Bid ProjectorNext.Equivariance
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)

def size (N p b m:ℕ) (s:ℝ) := ⌈((s+2)*R.family.S.scale m)/(R.family.path.rep N p b).p.supportExponent⌉₊

theorem charge (h:ℕ) (r:ℕ→ℝ) (rate:RateIs atTop R.family.S.scale r (-h)) (s C:ℝ) :
    ∀ᶠ m:ℕ in atTop, ∀ N p b, C*Real.exp (-((R.family.path.rep N p b).p.supportExponent*(size R N p b m s)))*r m ≤
        (R.family.S.a m)^h*Real.exp (-s*R.family.S.scale m) := by
  let S:=R.family.S
  have money:= rate.pays S.divergent (1-h) (by linarith)
  have fixed:∀ᶠ m:ℕ in atTop,C≤Real.exp (S.scale m) := (Real.tendsto_exp_atTop.comp S.divergent).eventually_ge_atTop C
  filter_upwards [money,fixed,rate.pos] with m booked cap rp
  intro N p b
  let t:=S.scale m
  let α:=(R.family.path.rep N p b).p.supportExponent
  have positive:0<α:=(R.family.path.rep N p b).p.exponent_pos
  have length:(s+2)*t≤(size R N p b m s)*α:= (div_le_iff₀ positive).mp (Nat.le_ceil _)
  have cut:Real.exp (-(α*(size R N p b m s)))≤Real.exp (-(s+2)*t) := Real.exp_le_exp.mpr (by linarith only [length,mul_comm α (size R N p b m s)])
  have base:(S.a m)^h=Real.exp (-(h:ℝ)*t):=by
    have unit:S.a m=Real.exp (-t) :=by simp [t,Schedule.scale,Real.log_inv,Real.exp_log (S.a_pos m)]
    rw [unit,←Real.exp_nat_mul];congr 1;ring
  calc C*Real.exp (-(α*(size R N p b m s)))*r m ≤ (Real.exp t*Real.exp (-(s+2)*t))*Real.exp ((1-h)*t) :=
          mul_le_mul (mul_le_mul cap cut (Real.exp_pos _).le (Real.exp_pos _).le) ((le_abs_self _).trans booked) rp.le (by positivity)
       _=(S.a m)^h*Real.exp (-s*t) :=by rw [base];simp only [←Real.exp_add];congr 1;ring

/-- This is the numerical nonlinear ray of the full normalized Wilson state throughout the aperture. -/
def reading {N p b:ℕ} (T:Slices R.family.path.levels p) (live:b<N) (h:ℕ) (Y:Config G (R.family.side N p)→ℂ)
    (t:Probe G h) (L:ℕ) := iteratedDeriv t.2.val ((WilsonMacroscopicRichReportedPosterior.observation R T live.le h Y) ∘
      WilsonMacroscopicRichCroppedProbe.fields (WilsonMacroscopicRichCroppedDeposit.window R N p b h L) R.family.params h 0
        ((R.family.path.rep N p b).p.threshold • t.1)) 0

theorem tested (h:ℕ) (t:Probe G h) (r:ℕ→ℝ) (rate:RateIs atTop R.family.S.scale r (-h)) (s:ℝ) :
    ∀ᶠ m:ℕ in atTop, ∀ (N p b:ℕ) (T:Slices R.family.path.levels p) (live:b<N) (_:Opened R.family h b p)
      (Y:Config G (R.family.side N p)→ℂ) (_:Continuous Y) (_:GaugeInvariant Y)
      (q:store R.family h p b) (_:reads h N p b q (r m)) (_:credit R.family N p h Y b live.le=value (C:=R.family) h N p b q),
      ‖runProbe (R.family.labels.level h) t (readPage R.family N p h Y b live.le) - reading R T live h Y t (size R N p b m s)‖ ≤
        (R.family.S.a m)^h*Real.exp (-s*R.family.S.scale m) :=by
  obtain ⟨C,_,localize⟩:=WilsonMacroscopicRichCroppedDeposit.measured R h t
  filter_upwards [charge R h r rate s C] with m bill
  intro N p b T live door Y ct gi q read joined
  rw [(WilsonMacroscopicRichCaptureWrap.measured R T live h Y ct gi door q (r m) read joined).2 t]
  exact (localize N p b T live door.post Y ct gi q (r m) read joined _).trans (bill ..)

end YM.Integration.WilsonMacroscopicRichAperture
