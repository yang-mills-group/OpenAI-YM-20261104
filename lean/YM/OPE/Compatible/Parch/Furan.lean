import YM.OPE.Compatible.Parch.Talent
/-!
# Growth. Stage families, budget IK
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom
variable {i j d k m r l b:ℕ}
open Next.Rank.Spindle
variable {I:Type}{o:I→ Cover}{B m:I→ℕ}{p:I→ Finset Cover}{L:Filter I}{n:I→ Side}{C:I→ℝ}
variable (P:∀ i,Prom (p i) (o i) (m i)) (T:(i:I)→Bid.Dir G (n i)→ ℝ)(hv:∀ i,p i⊆Lattice.box (B i))(hc:∀ i,Board (n i) (B i))
variable (he:Tendsto C L atTop)(h:RateLE L C (fun i=>(m i:ℝ)) 0)
noncomputable def turf_ (i:I):Tray G (p i)→ℝ:=fun x=> T i (dressQ (B i) (hv i) (hc i) x)
variable (ht:Bills L C T)(hd:∀ᶠ i in L,Tall (T i) d)
local notation "pk" i:arg=>Oasis (P i) (B i) (hv i) (hc i) (T i)
set_option quotPrecheck false
include h ht he hd
lemma Mahal (k:ℕ):Bills L C (fun i=>Claw.rank (pk i) k):=by
       let f(i):=turf_ T hv hc i; have hh: Bills L C f:=by obtain ⟨F,hF,H⟩:=ht; exact ⟨F,hF,H.mono fun i hi x hx=>hi _ ((frame_e G _ (cross_mono (hv i)) (hc i) x).trans hx)⟩
       have hT :∀ᶠ i in L,Tall (f i) d:=hd.mono fun i hi=> Tall.map (dressQ _ (hv _) (hc _)) hi
       let Q:= (range (k+1)); let μ(i):= ∑ j∈Q, ‖iteratedFDeriv ℝ j (f i) 0‖; have hm : RateLE L C μ 0:= RateLE.sum (f:=fun j i=> ‖iteratedFDeriv ℝ j (f i) 0‖) he (fun i _=> Floral f he hh hT i)
       choose B₀ hB H using boom G; let z(i j):= B₀ j*((m i:ℝ)+1)^j; let Y(i):= 1+∑ j∈Q, z i j; have hY(i):1≤ Y i:= le_add_of_nonneg_right (sum_nonneg (fun _ _=> mul_nonneg (hB _) (by positivity))) -- z
       have hw : RateLE L C Y 0:= (RateLE.const (1:ℝ) he).add (RateLE.sum (S:=Q) (f:=fun j i=> z i j) he (fun j _=>((RateLE.const (B₀ j) he).mul ((h.add (RateLE.const (1:ℝ) he) he).pow j he)).mono (by norm_num))) he
       let D:=(k.factorial:ℝ); have hD:0<D:= by unfold D; positivity
       refine ⟨fun i=>‖D⁻¹‖*(D* μ i * (Y i)^k),((RateLE.const ‖D⁻¹‖ he).mul (((RateLE.const D he).mul hm).mul (hw.pow _ he))).mono (by norm_num),hT.mono fun i hi x hx=>?_⟩
       let V(t:ℝ):= (P i).brood (t • x); have hr:pk i=f i ∘ (P i).brood:=rfl; have hU:ContDiff ℝ ω (pk i):=hr.symm ▸ hi.neat.comp ((P i).bliss G)
       change ‖Claw.rank (pk i) k x‖ ≤ _; unfold Claw.rank; rw [← WardBin.leading_tensor _ _ (hU.of_le le_top|>.contDiffAt)]; unfold WardBin.leading; change ‖D⁻¹ • iteratedDeriv k (f i ∘ V) 0‖≤_ ; rw[norm_smul,← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); refine strap V (f i) 0 _ (((P i).bliss G|>.comp (contDiff_id.smul contDiff_const)).of_le le_top|>.contDiffAt) (hi.neat.of_le le_top|>.contDiffAt) _ _ (fun j hj=>?_ ) (fun j hj ht=>?_)
       · rw [show V 0=0 from by unfold V; rw [zero_smul,air]]; exact single_le_sum (f:=fun j=> ‖iteratedFDeriv ℝ j (f i) 0‖) (fun _ _=>norm_nonneg _) (mem_range.mpr (by omega))
       calc
            _ ≤ z i j:= H j (p i) (m i) (o i) (P i) x hx
            _ ≤ ∑ j∈Q,z i j:= single_le_sum (fun j _=>mul_nonneg (hB j) (show 0 ≤ ((m i:ℝ)+1)^j by positivity)) (show j∈Q from mem_range.mpr (by omega)) -- f explicit
            _ ≤ Y i := le_add_of_nonneg_left zero_le_one
            _ ≤ (Y i)^j := (pow_one _).symm.trans_le (pow_le_pow_right₀ (hY i) hj)
lemma Basin (k:ℕ): Tonic C L (fun i=> pk i) k:=by obtain ⟨f,hf,H⟩:=blissP (fun i=>pk i) he (Mahal P T hv hc he h ht hd k) (hd.mono fun i hi=> (schoolC (P i) _ (hv i) (hc i) _ hi.neat).contDiffAt); exact ⟨f,hf,H⟩
omit h ht hd
include hv in lemma aridK (hX:RateLE L C (fun i=>(B i:ℝ)) 0):Arid C L (fun (i:I) (j:↥(crossV (p i)))=>j.val):=by
       constructor
       · let F(i):= ((2*(B i:ℝ)+1)^4)*4; have hx:RateLE L C F 0:= (((((RateLE.const (2:ℝ) he).mul hX).mono (by norm_num)|>.add (RateLE.const _ he) he).pow 4 he).mul (RateLE.const 4 he)).mono (by norm_num); apply hx.of_norm_le; filter_upwards with i; rw [Real.norm_of_nonneg (by positivity), Fintype.card_coe]; unfold F; exact_mod_cast (show (crossV (p i)).card ≤ (2*B i+1)^4*4 from (cross_amt _).trans (Nat.mul_le_mul_right 4 ((card_le_card (hv i)).trans (Terp.plunge _|>.le))))
       let x(i):ℕ:=1+4*(B i); refine ⟨x,?_,?_⟩
       · unfold x; push_cast; exact (RateLE.const (1:ℝ) he).add (((RateLE.const (4:ℝ) he).mul hX).mono (by norm_num)) he
       filter_upwards with i j; exact Nat.add_le_add_left (bounded (hv _ ((cross_def _).1 j.property|>.1))) _
end YM.OPE.Merchant
