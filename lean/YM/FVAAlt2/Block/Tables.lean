import YM.FVAAlt2.Block.Census
import YM.Comparison.RG02.Bulk.Fk
import YM.FormalOPE.RG10.InversionTop -- into
import YM.FormalOPE.RG10.Reclosure
/-! # Ordinary Fk on the actual period and connection to `FlatFeed`/cumulants

This step is the on-cover one (no inversion projection). No forest substitution, use all Free
 links, P(hessian) from this b & S, Bodies include determinant in U in `J` chart (NOT site zero
 mode projection). Fixed coarse field unrestricted; only Hessian OF THIS CONDITIONAL STEP, includes
 block penalty. Vertices carry the Haar germs already in the logarithm. Components of L(x) in
 exact `Census V` with power (the Laurent lowering) per HOT generator, usual plus sign. Rank zero
 & all multiplicities kept. Tag fixed; `Fk.fkChoice` gives equality for other tags of same F.
 Huge fixed periods & finite expansions: compute NoHole ≠ dropping Gaussian directions.
 All equations without analytical dependence: these make sense (even `assembly.gather`
 integrability) as polynomial Gaussian statements without the real estimates on W. Interpret
 `Fk` on `Well W` if restoring the nonnegative-power series by undoing Laurent lowering; no
 `Well` or orders of convergence asserted for arbitrary generators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Block
open Gauge Lattice Wilson Exterior Tree Precision RG
open Comparison.RG02 FormalOPE.RG10 Marker Multi Extra.Trajectories PowerSeries Next.SectorChange
open Finset Function Filter MeasureTheory PertExtension PertExtension.Series PertExtension.Series.Radial
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f :Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G} (K:Bulk.Kernel S p P O)(F: Forest S.ratio)(t:S.Choices)
variable (A:fieldDir G c 1)
variable {V:Type}[Fintype V][DecidableEq V]{R:Census V}(W:Bulk.Colors R G f)
local notation "L"=> Precision.Key F G → ℝ
local notation "χ"=> Bulk.translated K F A
local notation "φ"=> Bulk.geometric K F t W
local notation "Σk"=> K.covariance F t
local notation "μ"=> Gaussian.cloud Σk

-- the normalization really happens after integration of all these internal link variables. Unit tag.
-- the price stays separately `ground` etc.
def naked : FlatFeed Unit (L) where
   base _:= μ
   density _:= fun _=> 1
   mass_pos _:= by simp
   density_integrable _:= by simp
   density_nonneg _:= by simp
   chance _:= 1
   chance_nonneg _:= by simp
   chance_one:= by simp
lemma naked_mean (z:Unit × L → ℂ): (naked K F t).mean z= ∫ x,z ((),x) ∂μ:= by simp [FlatFeed.mean,naked]
def action : Vertices (Unit × L) where
   J:= 1
   V z:= InversionTop.into (PowerSeries.mk fun j=> Radial.layers φ j (χ z.2))
   J0:= by funext i; change coeff 0 (1:PowerSeries ℂ)=1; simp
   V0:= by funext i; simp [row]
def outputLog (z:Unit × L) := Assembly.curve W.power (Bulk.markFn S F W) (χ z.2)
def columns (z:Unit × L) := Word.expMark (outputLog K F A W z)
lemma generator (i:Multi.Hot R)(k:ℕ)(z:Unit × L) : row k (Word.read i.val (outputLog K F A W)) z = Assembly.jet (Bulk.markFn S F W i) (W.power i+k) (χ z.2):= by
   rw [row,Word.read,Function.comp_apply, Word.unfold_see, outputLog, Assembly.curve, coeff_mk]; exact Multi.part_lit _ _
lemma upright (z : Unit × L) : Word.vac R (outputLog K F A W z)=0 := by ext n; exact (Word.unfold_see ..).trans ((Assembly.mark_curve_quiet ..).trans (map_zero _).symm)
lemma columns_raw : Word.read R.quiet (columns K F A W)=1:= funext fun z=> Word.vac_exp _ (upright K F A W z)
lemma action_weight (z:Unit × L): (action K F t A W).weight z= InversionTop.into (PowerSeries.mk fun k=> Radial.expsum (layers φ) k k (χ z.2)) := by
   -- unchanged radial rescaling, no independence across marks.
   let U:= PowerSeries.mk fun j=> layers φ j (χ z.2)
   have h (k j): coeff j (U^k)= Zone.TaylorPow (layers φ) k j (χ z.2) := by
      induction k generalizing j with
      | zero=> simp [Zone.TaylorPow]
      | succ k ih=> simp [pow_succ,coeff_mul,Zone.TaylorPow,Zone.mul,ih,U]
   change expTaylor (InversionTop.into U) * 1=_; rw [mul_one]
   ext j : 1
   simp only [expTaylor, coeff_mk, InversionTop.into_coeff, expsum, Complex.ofReal_sum]
   apply Finset.sum_congr rfl; intro i _; rw [← map_pow, InversionTop.into_coeff,h]; push_cast; rfl
lemma exact_kernel (z:Unit × L): FlatFeed.totalize (action K F t A W) (columns K F A W) z = Assembly.expansions W.power (Bulk.markFn S F W) φ (χ z.2):= by
   unfold Assembly.expansions FlatFeed.totalize; congr 1
   · apply Word.observe_ext; intro s
     rw [action_weight, Word.see_sing]
     ext n
     rw [Word.unfold_see, Assembly.realCoeff, Assembly.beads]
     split_ifs <;> simp
lemma rowwise (s:R.Mode)(k:ℕ)(z:Unit × L): row k (Word.read s (FlatFeed.totalize (action K F t A W) (columns K F A W))) z= Assembly.insideMoment (Bulk.stage K F A) (Bulk.hinge F) W.power (Bulk.markFn S F W) φ s k z.2 := by
   rw [row,Word.read,Function.comp_apply, exact_kernel, Word.unfold_see]; rfl
lemma pays : FlatFeed.markedFunded (naked K F t) (action K F t A W) (columns K F A W):= by
   intro s k e
   rcases e with ⟨⟩
   unfold naked
   simp_rw [Complex.ofReal_one,one_mul,rowwise]
   have h:=(Assembly.gather (Bulk.stage K F A) (Bulk.hinge F) W.power (Bulk.markFn S F W) φ _ (K.symm F t) (K.positive F t) s (Order.pick k k)).1
   rw [Order.picked k le_rfl] at h; exact h
local notation "Λ" => (naked K F t)
local notation "Φv" => (action K F t A W)
local notation "Φm" => (columns K F A W)
-- totalized still common numerator
set_option quotPrecheck false
local notation "Xr" => (Λ).columns (FlatFeed.totalize Φv Φm)
local notation "Ω" => Word.sing R.quiet ((Λ).den Φv)
variable (n:ℕ)
lemma raw : Order.series R n Xr= Bulk.Fk K F t W A n:= by
    apply Order.Join.both_parts; intro s x
    rw [Order.polarization, ← Word.unfold_see, FlatFeed.column_eq, FlatFeed.average_coeff, Bulk.table,naked_mean]; simp_rw [rowwise]; rfl
lemma purity : Word.vac R Xr= (Λ).den Φv:= by rw [Word.vac_eq,FlatFeed.column_eq, FlatFeed.totalize_read, columns_raw,mul_one]; rfl
lemma vacuum : Order.series R n Ω= Order.denominator (Bulk.Fk K F t W A n):= by
    rw [← purity, ← peel, ← raw,Order.denominator,Order.bottom_map]
lemma positive_normalization : Order.series R n ((Λ).close Φv Φm)= Order.ratio (Bulk.Fk K F t W A n) := by
    refine Order.ratio_unique (Bulk.fk_unit ..) ?_
    rw [← vacuum,← map_mul,←raw]; congr 1
    apply Word.observe_ext; intro s
    rw [Word.spike_mul, FlatFeed.column_eq,FlatFeed.close_part,FlatFeed.step_den,FlatFeed.totalize_read]
lemma positive_marks : Order.series R n ((Λ).contraction Φv Φm)= Order.logMarked (Bulk.Fk K F t W A n):= by
    rw [FlatFeed.contraction, series_log, positive_normalization]; rfl
    rw [Word.boot, FlatFeed.preserve_one Λ Φv (columns_raw K F A W)]; simp
lemma vacuum_book : Order.series R n (Word.logWord Ω)= Order.logVac (Bulk.Fk K F t W A n):= by
    rw [series_log,vacuum]; rfl
    rw [Word.boot,Word.vac_eq, Word.see_sing, if_pos rfl, FlatFeed.den0]
end YM.FVAAlt2.Block
