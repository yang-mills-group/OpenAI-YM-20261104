import YM.RG05Readout.Velvet.Lance
import YM.RG05Readout.Chalice.Choir
/-! Passing signed read through `Final` arranged as whole profile test.
 exact normalized Boltzmann moments on cutoff.C. Pays any given eligible replicated license.Art. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction WithLp Nuclear Bay Cells Harvest Halls
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{i m n j b d k ℓ t t' v N p:ℕ}
    {Q q R r η ζ B':ℝ}(h:C.Makes)
local notation "δ"=> C.S.a
local notation "I"=> Fin v
local notation "P"=> (i:I)→Palette C
local notation "Φ'"=> Wave (Fin v)
variable (F:Wave (Fin v))(s:Fin v→ℕ)
section
open Petals Chalice
variable (D:Poem C j)
variable (hp:Sky F R η)(he:0<q)(hQ:R*q<C.S.a j/2)
local notation "S"=> s
local notation "g"=> D.opening
local notation "E"=> molten F q (boxC D)
local notation "Z"=> (C.side N p)
variable (X:(i:Fin v)→ Petals.Leafage C (s i))
local notation "p'"=>telegram D hp he hQ
local notation "P!"=> fun i:Fin v=> X i (N,p)
lemma branching (x:Fin D.n→E4): branch p' x= pluck D (points x) • E:=by
    apply Subtype.ext; funext u; rw [bridged]; have hv:= telegram_read hp D he hQ (points u) (points x); exact hv.trans (mul_comm ..)
lemma repaid : preamble D N p (physicalEra q F g C m p N s P!)=(∏ _i:Fin v,(q:ℂ)⁻¹^4) * jointS p' s X D.token m N p:=by
    rw [waves s P! F q (boxC D) m]; unfold preamble jointS; rw [mul_left_comm _ ((C.S.a N:ℂ)^_ )]; apply congr_arg; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _=> ?_); unfold column moment sees; rw [branching,map_smul]; let pp:ℂ:=pluck D (points (C.S.place ∘ x)); simp_rw [Pi.smul_apply, smul_eq_mul,mul_assoc,integral_const_mul]; exact mul_left_comm pp _ _
include h
lemma seen_knobs (v:Palette C d)(i:Address.Mark C d)(z:Site (C.side N p)):Continuous (key C N p d v i z):=by
    rw [Petals.pulses_key (C:=C) (p:=p) (N:=N) _ h z v]; exact (C.continuousO ..).const_smul _
    -- infer
lemma ripple : Continuous ((multi C m N p s P!) F) :=by
    unfold multi; rw [LinearMap.smul_apply]; apply Continuous.const_smul; rw [LinearMap.sum_apply]; simp_rw [Finset.sum_fn]; apply continuous_finsetSum; intro z _
    apply continuous_finsetSum _ (fun i _=> Continuous.mul continuous_const (continuous_finsetProd (ι:=Fin v) _ (fun j _=>?_))); exact seen_knobs h _ _ _
lemma sweep (q:ℝ): Continuous (physicalEra q F g C m p N s P!):=by rw [waves s P! _ _ (boxC D)]; exact (ripple h _ s X).const_smul _
end
section
open MergeProof Petals Petals.Kernel Next.Extract
lemma quoted (w:ℂ)(r:ℝ) (M: (i:I)→ Palette C (s i)) (g:Body): physicalEra r F (w • g) C m p N s M = w • physicalEra r F g C m p N s M:=by
    unfold physicalEra; funext u; change (∏ i:I,_) * (∫ z:E4, (w*g.val z)* _) = w* _; simp_rw [mul_assoc,integral_const_mul]; exact mul_left_comm ..
variable {f:Extraction.Order} (L:Poem C j)(H: CenterPort C f)
local notation "g"=> L.opening
local notation "h!"=> (C.S.a j/8)
lemma opening_gain (d:ℕ) : ∃ a:ℝ,0<a∧∃g':Body,g =(a:ℂ) • g'∧ Tall (E:=E4) g' (d+2) 1 1∧ ∀ x∈tsupport g'.val, ‖x‖ ≤ C.S.a j/8:=by
   obtain ⟨a,ha,hx⟩:= tall_any (u:=g) (boxC L) (d+2); let v:ℂ:=a; let u:=v⁻¹ • L.opening; have hv:v≠0:=Complex.ofReal_ne_zero.mpr ha.ne'
   have hU:Tall (E:=E4) u (d+2) 1 1:=by
       intro i hi x; rw [show u.val= v⁻¹ • L.opening.val from rfl, iteratedFDeriv_const_smul_apply (body_smooth ..|>.contDiffAt),norm_smul]; refine (mul_le_mul_of_nonneg_left (hx i hi _) (norm_nonneg _)).trans ?_; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg ha.le,one_pow,one_mul,one_mul,inv_mul_cancel₀ ha.ne'] -- check
   refine ⟨a,ha,u,(smul_inv_smul₀ hv _).symm,hU,fun x hx=>?_⟩; apply le_trans _ (show C.S.a j/16 ≤ C.S.a j/8 from by have h:=C.S.a_pos j; linarith); rw [← dist_zero_right]; exact Metric.mem_closedBall.mp (L.opening_there (Nuclear.scaled_support v⁻¹ L.opening hx))
variable (X:(i:Fin v)→ Palette C (s i))
-- future supply exact.Report eligible.
end
end YM.RG05Readout.Velvet
