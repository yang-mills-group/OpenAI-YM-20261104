import YM.RG01.Vacuum.Purchase
import YM.RG01.Vacuum.Flat

/-!
# Full hard expense on the actual common step

Observe that the Tender reserve `Payments.Rates` cannot pay a hard input
larger than the returned fee. Thus even on a schedule purchased only for
the older low order, the *entire* prealignment vacuum hard amount is flat
in coupling (uniform m and N), and still flat with a forced divisor. Note
these activities use actual measured flags (no analytic continuation). This
is before any new mask re-expression or insertion, and doesn't cover long
paths which do not retain that reserve in unforced log clusters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe
open Real
variable {G : Gauge} {X: Metals G} {D: Rolls X.p} {A : Alloy X D} (R:Factor A)
    {m : ℕ}

lemma returnsPrice {b : ℕ} {w a s k} (h : Payments.Rates b w a s k) : a ≤ w := by
  apply le_trans _ h.returns
  unfold Bid.quote Payments.inflation
  have hh := Real.add_one_le_exp (Real.exp k * a + 2*s)
  calc
    a = Real.exp (-k) * (Real.exp k * a) := by rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [h.soft,hh]) (Real.exp_pos _).le

lemma forecast_le (N : ℕ) (hm : m < N) (b : ℝ) (hb : b ∈ band A.B.a (m+1)) :
    forecastK A.B.a m R.scout b ≤ A.B.a.clock.forcedAllowance m := by
  let i:= A.B.a.clock.J m; let j:= A.B.a.clock.J (m+1)
  let a:= A.B.a; let r:=a.budget m; let u:=a.clock.hatBeta m; let y:=a.clock.hatBeta (m+1)
  let B:=A.B
  let M:=R.machine
  obtain ⟨ho,_,_,he,hE,_,ht⟩ := Deployment.clock_eqns a.clock m
  have h' := M.shops _ _ (B.valid.pays m) _ (step_paid B.a m)
  have hu : y=u+G.slopeConstant*Real.log (D.L j).val := by rw [← Push.PriceCompiler.block_eq B.valid]; exact (Deployment.hat m).symm
  have hp : r.B = Next.Scheduling.Clock.cover u := rfl
  have hs : X.p.profile i = a.params m := (params_eq B.valid m).symm
  have ha : Time.Same (a.params m) r := ⟨rfl,rfl,rfl⟩
  obtain ⟨hD,hW,hK⟩ := h' r (hs.symm ▸ ha) hp ht
  have hf:= M.coverage _ _ (step_paid B.a m)
  have hM := hK (R.exchange j i) (B.kin.alpha N m) (a.clock.theta j) b (UVNext.CouplingReset.within_alpha hm) (hu ▸ trial_in hb)
  obtain ⟨v,k,hv,hg⟩:= hM.2.2.1.hard
  have hM' := (hM.2.2.2 hf.1).2
  apply le_trans (b:= Instrument.plain.w (a.clock.hatBeta m)) _ hE.ge
  convert! (returnsPrice hg).trans hM' using 1
  dsimp only [forecastK,B,j,i] at * -- expensive!
  rw [← hu]

lemma hard_le (N : ℕ) (hm : m < N) (b : ℝ) (hb : b ∈ band A.B.a (m+1)) :
    hardPrice R m b ≤ A.B.a.clock.forcedAllowance m:= by
  unfold hardPrice
  have he:= forecast_le R N hm b hb
  have hp: 0 < A.B.a.clock.forcedAllowance m:=Real.exp_pos _
  linarith

/-- Retaining the divisor, beats every given fine-coupling power on the
schedule. Universal in G and N after fixing the shared levels (C existential
constant in statement; doesn't have to grow with period or cutoff depth).
-/
theorem hardDivided (hG:G.Simple) (d k:ℕ) : ∃ c : ℝ, 0≤c ∧ ∀ (m N : ℕ), m<N → ∀ b ∈ band A.B.a (m+1),
    A.B.a.clock.hatBeta (m+1)^k * (hardPrice R m b / Real.sqrt (A.B.a.clock.forcedAllowance m)) ≤ c * (Real.sqrt b)⁻¹^d := by
  obtain ⟨C,hC,h⟩:=Flat.currency A.B.a hG d k
  refine ⟨C,hC,?_⟩
  intro m N hm b hb
  have ht : 0 < A.B.a.clock.forcedAllowance m := Real.exp_pos _
  have hL : 1 < A.B.a.clock.hatBeta (m+1):= A.B.a.fits.delayed _
  have hy:= hard_le R N hm b hb
  apply le_trans _ (h m b (lt_of_lt_of_le (half_pos (zero_lt_one.trans hL)) hb.1) (.inl hb.2))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_iff₀ (Real.sqrt_pos.mpr ht),Real.mul_self_sqrt ht.le]
  exact hy

end YM.RG01.Vacuum
