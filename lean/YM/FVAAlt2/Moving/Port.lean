import YM.FVAAlt2.Sound.From
import YM.FVAAlt2.Moving.Mesh
/-! # Positions on actual ORBIT (not PERIODIC) grid. Valid array of sample paths at all times. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Moving.CalendarT
open Function Set Filter MeasureTheory Real Topology
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound
open MS MS.Land MS.Dial MS.Rake MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open PowerSeries Integration RunFormalChain FormalOPE Pipeline Pipeline.See
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {X:Type} (T: Lodge.Track X) {l:Filter X}{n:ℕ} (a:X → Cover) -- parser C
noncomputable abbrev page (i:X):= T.size ( Page.opening _ i )
noncomputable abbrev δ (i:X):= Sound.Alone T i
def Unitμ (μ:ℝ):= (T.PoseT μ a (fun _ : Fin n=> a) ).profile
lemma ports (h:Tendsto T.batch l atTop): MeshT.Invoices (δ T) (page T) l:= by
   have hΘ:=T.θ_runs h; refine ⟨fun i=> exp_pos _, tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hΘ),?_⟩
   apply tendsto_atTop_mono' l _ (tendsto_exp_atTop.comp hΘ ); filter_upwards [T.super l h 2] with i hi
   change exp (T.Θ i) ≤ exp (-(T.Θ i))*(( (page T i).val:ℕ):ℝ ); rw [Real.exp_neg, ← div_eq_inv_mul]; apply (le_div_iff₀ (exp_pos _)).mpr; rw [← exp_add,← two_mul]; refine (exp_monotone hi).trans_eq ?_; rw [Real.exp_log ( δ_p _ i ), Vista.tickA, T.payments]
   -- fill
abbrev nativeT (x:X)(n:ℕ):= MeshT.offsets (page T x) n
variable {T}
abbrev sample (x: X) (w:nativeT T x n):= MeshT.scenes (δ T x) w
lemma realize_t (x:X)(w:nativeT T x n): Home.Profiles.realize (sample x w)= fun i=> δ T x • Tone.embed ( Lattice.lift (w i) ):=rfl
-- extrapolate choice to available path with same physical support hull. Need not be always on offsets.
variable {K:Set (Points n)}{μ:ℝ}{f: Fin n→ X→ Cover}
-- economy when testP already uniformly separated.Buys from compact on QP not Points. We sometimes permit cheap fallback not in K. choose fallback.B.Area.Snap.Can pick anytime not on grid.
lemma tag_econ {A: Set (Fin n→QP)} (ha:IsCompact A)(hm:∀ x∈A,Injective x)(ht:∀ i:X,testP (T.PoseT μ a f) i∈A) : let R:= T.PoseT μ a f; MS.Tide.Profile R.profile f ∧ Rake.Mesh R.profile (Fleet.info f):= by
 intro R; have hf(x:X)(w:Fin n): ‖testP R x w‖= exp (-R.profile.θ x) * ‖Tone.embed ( f w x )‖:= norm_smul_of_nonneg (exp_pos _|>.le) _
 constructor
 · intro w; let g (f:Fin n→QP):= ‖f w‖; obtain ⟨C,hC⟩:= (ha.image (show Continuous g from (continuous_apply w).norm)).bddAbove; refine ⟨max 1 C,lt_max_of_lt_left zero_lt_one,fun i=>?_⟩
   have hz:g (testP R i) ≤ max 1 C:= le_trans (hC (Set.mem_image_of_mem g ( ht i ))) ( le_max_right .. ); unfold g at hz; rw [hf,Real.exp_neg,← div_eq_inv_mul] at hz; exact (div_le_iff₀ (exp_pos _)).mp hz
 apply Dial.unpose (v:=μ); intro i j hij
 let U (x:Fin n→QP):= ‖x i-x j‖; have ht' : Continuous U:=( Continuous.sub (continuous_apply i) (continuous_apply j) ).norm; obtain ⟨B,hB⟩:= (ha.image ht').bddAbove
 by_cases he:A.Nonempty
 · obtain ⟨k,hk,H⟩:= ha.exists_isMinOn he ht'.continuousOn; refine ⟨⟨max 1 B, lt_max_of_lt_left zero_lt_one,fun x=> ?_⟩,⟨ U k, norm_pos_iff.mpr (sub_ne_zero.mpr (hm k hk|>.ne hij)), fun x=>?_ ⟩⟩ <;> (simp only [Rake.Geo.roots,Pi.zero_apply, Real.exp_zero,mul_one]; first|exact ( H (ht x) ) | exact ( hB (Set.mem_image_of_mem U (ht x)) ).trans (le_max_right ..))
 exact ⟨⟨1,one_pos,fun x=> ( he ⟨_,ht x⟩ ).elim⟩,⟨1,one_pos,fun x=> (he ⟨ _,ht x⟩).elim ⟩⟩
-- universal fallback use penny scaling from Track exact.QP pose coordinates.Compute.If x chosen. testP uses off definition.
noncomputable def fallback (T:Track X) : Fin n → X→ Cover:= fun i x=> ( T.penny x ) • Track.landing i
def sampleE (i:Fin n):QP:= Tone.embed (Track.landing i)
lemma discount (μ:ℝ)(a:X→ Cover)(i:X): testP (T.PoseT μ a (fallback (n:=n) T)) i=sampleE:=by
 ext1 j; change δ _ i • Tone.embed ( (T.penny i) • Track.landing j )= _; unfold δ Sound.Alone sampleE
 rw [Real.exp_neg,show Tone.embed _= exp (T.Θ i) • Tone.embed ( Track.landing j ) from ?_, inv_smul_smul₀ (exp_pos _|>.ne') ]; funext v; rw [← T.expense]; simp [Tone.embed,Pi.smul_apply] -- proof Orientation ok
lemma reachable (x:X) : (sampleE (n:=n))=(testP (T.PoseT μ a (fallback T)) x):= (discount ..).symm -- use as style
lemma realistically (h:IsCompact K)(he:K⊆ YM.conf n)(hw:∀ i:X,testP (T.PoseT μ a f) i∈ realize '' K ∨ testP (T.PoseT μ a f) i= Moving.CalendarT.sampleE) : let R:= T.PoseT μ a f; MS.Tide.Profile R.profile f∧ Rake.Mesh R.profile (Fleet.info f):= by
 apply tag_econ a (A:=realize '' K∪{ Moving.CalendarT.sampleE }) ((h.image realize_s).union (isCompact_singleton)); rintro x (⟨y,H,rfl⟩|h); exact realize_one (he H)
 · exact (Set.mem_singleton_iff.mp h) ▸ Track.configs
 exact hw
end YM.RegulatorIR.FVAAlt2.Moving.CalendarT
