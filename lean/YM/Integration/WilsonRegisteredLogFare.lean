import YM.Integration.WilsonRegisteredWidthCurrency
import YM.Integration.WilsonRegisteredCenteredEarlier

/-! The actual earlier quota pays the full Taylor price with every fixed
inverse power of the logarithm, uniformly in the retained Taylor degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredLogFare
open Filter Lattice RG Wilson Precision PertExtension PhysicalNext.Repeat.Legato Pert.Asymptotics RG16
open WilsonRegisteredAffineSource WilsonRegisteredCenteredReading WilsonInheritedRegisteredField
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels

theorem column (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)  ≤  Real.log (Lambda (A) m)) :
    ∀ᶠ m:ℕ in atTop,((A).params (m+1)).columns  ≤  2*Real.log ((A).clock.hatBeta (m+1)) := by
  have logs:=(tendsto_add_atTop_nat 1).eventually ((WilsonAdmissionScale.logarithm_tendsto (A) simple).eventually_ge_atTop 2)
  filter_upwards [logs] with m late
  let s:=Real.log ((A).clock.hatBeta (m+1))
  have pos:0<Lambda (A) m:=by
    change 0<2+Real.log ((A).clock.hatBeta m)
    linarith only [Real.log_pos ((A).fits.delayed m)]
  have mono:Real.log ((A).clock.hatBeta m)  ≤  s:=WilsonAdmissionScale.logarithm_monotone (A) simple (Nat.le_succ m)
  have two:(2:ℝ)  ≤  s:=late
  calc
    _  ≤  ((R.family.S.block m).val:ℝ):=RG12.Commission.column_priced (A) m
    _  ≤  Real.log (Lambda (A) m):=slow m
    _  ≤  Lambda (A) m:=Real.log_le_self pos.le
    _  ≤  2*s:=by change 2+Real.log ((A).clock.hatBeta m)  ≤  2*s;linarith only [mono,two]

theorem purchased (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)  ≤  Real.log (Lambda (A) m))
    (d:ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀N per (live:m+1 ≤ N) (v:R.family.label 4) (o:Site (R.family.side (m+1) per))
      (q:ℕ) (η:ℂ→L[ℝ]ℝ),
    let s:=Real.log ((A).clock.hatBeta (m+1))
    s^d*fare R live v o q η  ≤  ε*(‖η‖*amplitude R m*Next.UVStress.quota R.family 4 (m+1) N per v) := by
  have one:=(tendsto_add_atTop_nat 1).eventually (WilsonRegisteredWidthCurrency.logarithmic R simple 0 zero_lt_one)
  have much:=(tendsto_add_atTop_nat 1).eventually (WilsonRegisteredWidthCurrency.logarithmic R simple (d+1) (half_pos he))
  filter_upwards [column R simple slow,one,much] with m hc h1 hd N per live v o q η s
  let w:=width R N per (m+1)
  let Z:=packet R.makes live v o
  let col:=((A).params (m+1)).columns
  let V:=(R.family.labels.level 4)
  let size:=V.coeffSize (V.core Z.x)
  let M:=Next.UVStress.quota R.family 4 (m+1) N per v
  let α:=amplitude R m
  have core:size  ≤  M:=by
    have normal:V.coeffSize Z.x=M:=
      congrArg V.coeffSize (WilsonTranslatedFactory.coordinate (C:=R.family) R.makes live o ((R.family.factory 4 N per).terminal.symm v))
    exact (Work.G08.size_core V Z.x).trans normal.le
  have s0:0 ≤ s:=(Real.log_pos ((A).fits.delayed _)).le
  have a0:0 ≤ α:=by dsimp [α,amplitude];positivity [R.family.S.a_pos (m+1)]
  have z0:0 ≤ size:=Work.G08.size_nonneg V _
  have c0:0 ≤ col:=zero_le_one.trans ((A).params (m+1)).columns_ge
  have w0:0 ≤ w:=(WilsonRegisteredWidthCurrency.band R N per (m+1) live).1
  have w1:w ≤ 1:=by simpa only [pow_zero,one_mul] using h1 N per live
  have aq:0 ≤ w^(q+1)/q.factorial:=by positivity
  have small:w^(q+1)/q.factorial  ≤  w:=by
    apply (div_le_self (pow_nonneg w0 _) (show (1:ℝ) ≤ q.factorial from by exact_mod_cast Nat.factorial_pos q)).trans
    simpa only [pow_one] using pow_le_pow_of_le_one w0 w1 (Nat.le_add_left 1 q)
  have out:s^(d+1)*w  ≤  ε/2:=hd N per live
  have issued:s^d*(col*(w^(q+1)/q.factorial))  ≤  ε:=by
    calc _  ≤  s^d*((2*s)*w):=
           mul_le_mul_of_nonneg_left (mul_le_mul hc small aq (by positivity)) (pow_nonneg s0 _)
         _ = 2*(s^(d+1)*w):=by rw [pow_succ];ring
         _  ≤  ε:=by linarith only [out]
  change s^d*(α*(‖η‖*(col*size*(w^(q+1)/q.factorial))))  ≤  ε*(‖η‖*α*M)
  calc
    _ = (s^d*(col*(w^(q+1)/q.factorial)))*(‖η‖*α*size):=by ring
    _  ≤  _:=mul_le_mul issued (mul_le_mul_of_nonneg_left core (by positivity)) (by positivity) he.le

end YM.Integration.WilsonRegisteredLogFare
end
