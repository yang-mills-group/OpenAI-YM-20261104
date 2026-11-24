import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Moments
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
/-!
# Sweep recovery at integer dimensions (all, not just large)

Actual extra Haar measure proof to $C_d$. Lemmas consume full dot radial Gaussian any etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {I E F G: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F]
variable {g:Tree E F}{m n k:ℕ}(h:Ultra g)(H:Reflect g)
def pitch (m:ℕ): ℝ:= π⁻¹ ^m * Nat.factorial m
include h H
lemma vanish (n:ℕ)(p:E): vault (pruning (n+1) g) p n=-((-2:ℝ)^n * Nat.factorial n) • g (0,p):= by
   induction n with
   | zero=> rw [spent,met,static h H]; simp
   | succ n ih=> obtain ⟨hV,hL⟩:= pruned h (fun _=>H) (n+1); rw [spent _ g, stairs hV (hL ()) n p,ih, smul_smul, Nat.factorial,pow_succ]; push_cast; ring_nf
lemma visit (m k:ℕ)(p:E): vault (pruning m g) p (k+m)=((-2:ℝ)^m * (Nat.factorial (k+m):ℝ)/(Nat.factorial k)) • vault g p k:= by
   induction m with
   | zero=> simp [Nat.factorial_ne_zero,met]
   | succ m ih=> obtain ⟨hr,hs⟩:= pruned h (fun _=>H) m; rw [spent _ g,← add_assoc, stairs hr (hs ()) (k+m) p,ih, smul_smul, Nat.factorial,pow_succ]; push_cast; ring_nf
variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
-- cpow
omit h H [CompleteSpace F] [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma fetched_nat (n:ℕ)(p:E): fetching g (cloud n) p=vault g p n:= by
   unfold fetching vault; refine integral_congr_ae (Eventually.of_forall fun t=>?_); unfold fetchP cloud; simp only; rw [show 2*(n:ℂ)+1=(( (2*n+1:ℕ):ℕ):ℂ) by push_cast; rfl, Complex.cpow_natCast, ← Complex.ofReal_pow]; exact IsScalarTower.algebraMap_smul ℂ (t^(2*n+1)) _ -- names
lemma core_static (n:ℕ)(p:E): coreC (cloud n) n g p=pitch n • g (0,p):= by
    rw [coreC,Pi.smul_apply,fetched_nat,vanish h H n p, smul_smul]; unfold pitch gage; congr 1; rw [pow_succ, show (- (2:ℝ)⁻¹)^n = ((-2:ℝ)^n)⁻¹ by simp only [← inv_neg,inv_pow] ]; field_simp -- at inverse power
variable (G:Type) [NormedAddCommGroup G] [InnerProductSpace ℝ G][FiniteDimensional ℝ G][MeasurableSpace G][BorelSpace G][Nontrivial G]
omit h H [CompleteSpace F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
lemma sphere_valid {k:ℕ}(p:ℝ→F)(hr:Module.finrank ℝ G=2*(k+1)): (∫ x:G,p ‖x‖)= ((2*(k+1:ℕ):ℝ) * (π^(k+1) / (Nat.factorial (k+1):ℝ))) • (∫ r in Ioi (0:ℝ), r^(2*k+1) • p r) := by
   rw [integral_fun_norm_addHaar,Measure.real, InnerProductSpace.volume_ball_of_dim_even hr _ _]; simp only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal (show 0≤π^(k+1)/(Nat.factorial (k+1):ℝ) by positivity),hr,show 2*(k+1)-1=2*k+1 by omega, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_mul]; push_cast; rfl -- inspect interfaces
lemma core_nat (hc:n=m+k+1)(hr:Module.finrank ℝ G=2*(k+1))(x:E): coreC (cloud n) m g x=pitch n • ∫ p:G,g (‖p‖,x):= by
   have hh : n=k+(m+1):=by omega
   rw [hh]; rw [coreC,Pi.smul_apply, fetched_nat,visit h H (m+1) k x,sphere_valid G (fun p=>g (p,x)) hr,smul_smul, smul_smul]; congr 1 -- rewrite name
   -- gage*(visit) = pitch n*sph
   unfold pitch gage; rw [show π⁻¹^(k+(m+1))=π⁻¹^m*(π^(k+1))⁻¹ by nth_rw 1 [show k+(m+1)=m+(k+1) by omega]; simp only [pow_add π⁻¹ m, inv_pow],show (- (2:ℝ)⁻¹)^(m+1) = ((-2:ℝ)^(m+1))⁻¹ by simp only [← inv_neg,inv_pow], Nat.factorial_succ k]; push_cast; field_simp
end YM.MS.Arc
