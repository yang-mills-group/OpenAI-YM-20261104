import YM.Integration.WilsonCapturedPrimaryEngineering

/-! The reporting dates for the actual section and finite-field inverse
are fixed without knowing the ultraviolet cutoff or the physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryTariff
open Filter Finset Lattice Wilson RG Source Labels Push.Local Extra.Histories
open PhysicalNext.Repeat.Legato Pert.Asymptotics RG16 Trace.Physical.Germ
open scoped Classical BigOperators Topology
variable {G : Gauge} {d : ℕ} (F : Frame G d) (A : Hol G)

theorem inverse (N : ℕ) : 0 ≤ WilsonCapturedPrimaryDecoder.invoice F A N :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (sum_nonneg fun p _ => WilsonCapturedPrimaryPanel.fee_nonneg A p N)

theorem panel (N : ℕ) : 0 ≤ WilsonCapturedPrimaryPredictionPanel.fee F N :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (sum_nonneg fun _ _ => WilsonCapturedPrimaryPolynomial.price_nonneg ..)

theorem wraps : 0 ≤ WilsonCapturedPrimaryCoreBill.wrapFee F A :=
  mul_nonneg (Nat.cast_nonneg _) (germ_close F A).choose_spec.1.le

theorem original {G : Gauge} (R : Run G) (simple : G.Simple) (d D' p h k : ℕ)
    (slow : ∀ m, ((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m)) :
    ∀ᶠ i:ℕ in atTop, ∀ N per, i<N →
      let g := regulatorRun R.family N per (i+1)
      let w := (R.family.path.levels.params i).columns
      let I := WilsonCapturedPrimaryDecoder.invoice ((Labels.frames G).level d) (Next.Foundations.hol G) D'
      1 ≤ (R.family.path.levels.budget i).supportExponent →
      0<g ∧ g≤1 ∧ w≤4/g^2 ∧ (I*g^(p+WilsonCapturedPrimaryEngineering.loss d h k))*w ≤ 1/2 := by
  let I := WilsonCapturedPrimaryDecoder.invoice ((Labels.frames G).level d) (Next.Foundations.hol G) D'
  have ip : 0 ≤ I := inverse ..
  filter_upwards [WilsonCapturedPrimarySection.priced R simple slow,
    WilsonCapturedPrimaryCourse.original R simple 0 0 (C:=8*I) (ε:=1)
      (mul_nonneg (by norm_num) ip) zero_lt_one] with i col paid
  intro N per cut g w I' support
  obtain ⟨pos,unit,_,_,fee⟩ := paid N per cut support
  have x : 8*I*g≤1 := by simpa using fee
  have one : g≤1 := unit.trans (by norm_num)
  exact ⟨pos,one,col N per cut,WilsonCapturedPrimaryEngineering.absorb pos one ip (col N per cut)
    x (by dsimp [WilsonCapturedPrimaryEngineering.loss];omega)⟩

end YM.Integration.WilsonCapturedPrimaryTariff
