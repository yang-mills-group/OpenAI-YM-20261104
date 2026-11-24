import YM.Agora26.Marks.Tail
import YM.Integration.WilsonReportMomentDifference
import YM.OPE.Log.Plans
import YM.Pert.Asymptotics.RawAxis

/-! The pre-report connected Wilson correlation. Each regular representative is
the one actually issued for its field, position and period. The measured signed
comparison for every subset is taken before the Möbius partition sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportSeparatedMoments
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Marker Multi
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open Extra.Trajectories (connected)
open WilsonReportMomentDifference
open scoped BigOperators Classical

variable {G : Gauge} {C : Family G} {W r D} {V : Type} [Fintype V] [DecidableEq V]

def fee (Γ : Census V) (s : Γ.Mode) (q : ℕ) : ℝ :=
  multiplicity Γ s * (1+3^(Fintype.card V))^(Fintype.card (Hot Γ)) * 2^q

omit [Fintype V] in
theorem count_nonneg (Γ : Census V) (s : Γ.Mode) : 0 ≤ multiplicity Γ s :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)

theorem fee_nonneg (Γ : Census V) (s : Γ.Mode) (q : ℕ) : 0 ≤ fee Γ s q :=
  mul_nonneg (mul_nonneg (count_nonneg Γ s) (by positivity)) (by positivity)

def gap (Γ : Census V) (d : V → ℕ) {k N p : ℕ} (hk : k ≤ N)
    (x : V → Site (C.side k p)) (v : (j : V) → C.label (d j)) (s : Γ.Mode) : ℂ :=
  (connected (microscopic Γ C (BarePack d x hk v))).part s -
  (connected (reported Γ C (N:=N) (regularPack (N:=N) d x v))).part s

private theorem budget (n h t q : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    (b^(q+(t+1)*n*h))⁻¹ * (1+(3*b^(t+1))^n)^h ≤
      (1+3^n)^h * (b^q)⁻¹ := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hp : 1+(3*b^(t+1))^n ≤ (1+3^n)*b^((t+1)*n) := by
    rw [mul_pow, ← pow_mul]
    calc
      _ ≤ b^((t+1)*n) + 3^n*b^((t+1)*n) := add_le_add (one_le_pow₀ hb) le_rfl
      _ = _ := by ring
  have grow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(3*b^(t+1))^n) hp h
  calc
    _ ≤ (b^(q+(t+1)*n*h))⁻¹ * ((1+3^n)*b^((t+1)*n))^h :=
      mul_le_mul_of_nonneg_left grow (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; field_simp

private theorem physical_rate (hC : C.Makes) {N p k : ℕ} (hk : k ≤ N) (q : ℕ) :
    ((C.path.levels.clock.hatBeta k)^q)⁻¹ ≤ 2^q*(Pert.Asymptotics.regulatorRun C N p k)^(2*q) := by
  let b := C.path.levels.clock.hatBeta k
  let a := C.path.β N p k
  have hb : 0 < b := zero_lt_one.trans (C.path.levels.fits.delayed k)
  have rep := (hC.wilson.represents N p k hk).band
  have low : b/2 ≤ a := rep.1
  have high : a ≤ 2*b := rep.2
  have ha : 0 < a := (half_pos hb).trans_le low
  have rate : b⁻¹ ≤ 2*(Pert.Asymptotics.regulatorRun C N p k)^2 := by
    change b⁻¹ ≤ 2*(Real.sqrt a)⁻¹^2
    rw [inv_pow, Real.sq_sqrt ha.le]
    field_simp
    linarith only [high]
  rw [← inv_pow, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hb.le) rate q

private theorem settle (n h t q : ℕ) {b g cost value : ℝ} (hb : 1 ≤ b)
    (hc : 0 ≤ cost) (hr : (b^q)⁻¹ ≤ 2^q*g^(2*q))
    (raw : value ≤ cost*(b^(q+(t+1)*n*h))⁻¹*(1+(3*b^(t+1))^n)^h) :
    value ≤ (cost*(1+3^n)^h*2^q)*g^(2*q) := by
  have cf : (0:ℝ) ≤ (1+3^n)^h := by positivity
  calc
    _ ≤ cost*((b^(q+(t+1)*n*h))⁻¹*(1+(3*b^(t+1))^n)^h) := raw.trans_eq (mul_assoc ..)
    _ ≤ cost*((1+3^n)^h*(b^q)⁻¹) := mul_le_mul_of_nonneg_left (budget n h t q hb) hc
    _ ≤ cost*((1+3^n)^h*(2^q*g^(2*q))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hr cf) hc
    _ = _ := by ring

/-- Choose arity, admitted products, input mass exponent, output order and
separation band before all cutoffs, periods, sites, and field labels. At each
of those choices, the error of the normalized connected moment is uniform in
the actual sectors, with the physical regulator coupling. -/
theorem purchased (hG : G.Simple) (hC : C.Makes) (hB : Log.OnBudget C.path.levels)
    (citizen : Citizen C W r D) (Γ : Census V) (d : V → ℕ) {br : ℕ} (hbr : 0 < br)
    (e t q : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ dis : ℕ,(C.path.levels.budget k).B^8 ≤ dis →
    (dis:ℝ) ≤ C.path.levels.clock.hatBeta k^e → ∀ N p : ℕ, ∀ hk : k<N,
    ∀ x : V → Site (C.side k p), Sites26 (C:=C) br dis x → ∀ v : (j : V) → C.label (d j),
    (∀ j,Spindle.paid C (d j) k N p (v j) ≤ C.path.levels.clock.hatBeta k^t) → ∀ s : Γ.Mode,
    ‖gap Γ d hk.le x v s‖ ≤ fee Γ s q * Pert.Asymptotics.regulatorRun C N p k^(2*q) := by
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  let n := Fintype.card V
  let h := Fintype.card (Hot Γ)
  let a := q+(t+1)*n*h
  filter_upwards [completeNative H citizen hbr d e t a,
    eventually_all.mpr (fun j : V => eventually_ge_atTop (C.ref (d j)))] with k hist refs
  intro dis lo hi N p hk x positions v labels s
  let b := C.path.levels.clock.hatBeta k
  have hb : 1 ≤ b := (C.path.levels.fits.delayed k).le
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  let E := (b^a)⁻¹
  have hE0 : 0 ≤ E := (inv_pos.mpr (pow_pos hb0 _)).le
  have hE1 : E ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hb)
  let M := 3*b^(t+1)
  have hM : 1 ≤ M := (one_le_pow₀ hb : 1 ≤ b^(t+1)).trans (le_mul_of_one_le_left (pow_nonneg hb0.le _) (by norm_num))
  have sup (j : V) (U : Config G (C.side k p)) : ‖regularPack (N:=N) d x v j U‖ ≤ M := by
    have bound := wholeSize H citizen (v j) (x j) hk (refs j) U
    apply bound.trans
    have price := mul_le_mul (hB.present k) (labels j) (paid_pos C (d j) k N p (v j)) hb0.le
    change 3*(_*_) ≤ 3*b^(t+1)
    rw [pow_succ, mul_comm (b^t) b]
    exact mul_le_mul_of_nonneg_left price (by norm_num)
  have diff := hist dis lo hi N p hk x positions v labels
  have raw := WilsonReportMomentDifference.original Γ C hC hk.le (BarePack d x hk.le v)
    (regularPack (N:=N) d x v) hE0 hE1 hM sup diff s
  exact settle n h t q hb (count_nonneg Γ s) (physical_rate hC hk.le q) raw

end YM.Integration.WilsonReportSeparatedMoments
end

