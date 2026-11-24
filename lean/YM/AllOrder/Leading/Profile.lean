import YM.AllOrder.Leading.Global

/-!
# Functional profile estimates from the all-length leading frame.
 Moving-leg lemma: finite-dimensional costs, scales throughout trail. Useful
 after applying the exact position solves or transferring trace.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Leading
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Trace.Terrace Analysis
open Trace.Over MergeProof.East Next.UVStress Maxwell Spin Next.Rank MeasureTheory
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
variable {n j : ℕ} {t : Fin n → ℕ}
local notation "free" => Bel C.book

/-- Generic filter version of `paired_limit`. -/
lemma profile_limit (u : Test n) {ι : Type*} {l : Filter ι} {f : ι → Points n → ℂ}
    {F : Points n → ℂ}
    (h : ∀ᶠ i in l, ContinuousOn (f i) (conf n)) (hf : ContinuousOn F (conf n))
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x ∈ tsupport u, ‖(f i - F) x‖ ≤ ε) :
    Tendsto (fun i => u.applyTo (f i)) l (𝓝 (u.applyTo F)) := by
  have hi : Integrable (fun x => ‖u x‖) := (u.continuous.integrable_of_hasCompactSupport u.hasCompactSupport).norm
  refine Metric.tendsto_nhds.mpr fun ε he => ?_
  let N := ∫ x, ‖u x‖
  have hn : 0≤N := integral_nonneg (fun _=> norm_nonneg _)
  let δ := ε/(N+1)
  have hd : 0<δ := div_pos he (by linarith)
  filter_upwards [hp _ hd,h] with i hi' hm
  have hv : ∀ x, ‖u x * (f i-F) x‖ ≤ ‖u x‖ * δ := fun x=> by
    by_cases hx : x∈ tsupport u
    · grw [norm_mul_le _ _,hi' _ hx]
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [dist_eq_norm,← Next.UVStress.test_sub _ _ hm hf]
  have h' := (norm_integral_le_integral_norm (fun x=> u x*(f i-F) x)).trans
      (integral_mono (u.smearing (hm.sub hf) |>.norm) (hi.mul_const δ) hv)
  rw [integral_mul_const] at h'; refine h'.trans_lt ?_
  change N*δ < ε; unfold δ
  calc N * (ε/(N+1)) = (N/(N+1))*ε := by ring
       _ < 1*ε := mul_lt_mul_of_pos_right ((div_lt_one (by positivity)).mpr (by linarith)) he
       _ = _ := one_mul _

lemma aligned_tests (hU : Aligned F g U) (v : Fin n → (free).Tag) (u : Test n) :
    Tendsto (fun r:ℝ => u.applyTo (tableRead (U r) r v)) trail (𝓝 (u.applyTo (disc v))) := by
  apply profile_limit u ((show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin).mono
      fun r hr => (smoothZoom F.room.kernel.smooth (panels _ ∘ v) hr).continuousOn)
     (smoothDisc (Free.hierarchy C.labels).smooth v).continuousOn
  intro ε he; filter_upwards [hU.jets n v 0 _ u.hasCompactSupport u.tsupport_subset he] with r hr x hx
  change ‖(tableRead (U r) r v-disc v) x‖≤ε
  rw [← norm_iteratedFDeriv_zero (𝕜:=ℝ), show iteratedFDeriv ℝ 0 (tableRead (U r) r v-disc v) x = iteratedFDeriv ℝ 0 (tableRead (U r) r v) x-iteratedFDeriv ℝ 0 (disc v) x from ContinuousMultilinearMap.ext fun _=>rfl]
  exact (hr x hx).le

section extension
variable {ι : Type*} {l : Filter ι} {K : Set (Points n)}

/-- Elementary extension of compact diagram bounds to moving-coefficient
finite sums, useful also after perturbative frame approximation. -/
def CompactSmall {M : Type*} [Norm M] (l : Filter ι) (K : Set (Points n)) (F : ι → Points n → M) : Prop :=
    ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ x∈K, ‖F i x‖<ε

namespace CompactSmall
variable {M : Type*} [SeminormedAddCommGroup M] {A B : ι → Points n → M}
lemma add (h : CompactSmall l K A) (h' : CompactSmall l K B) : CompactSmall l K (A+B) := by
  intro ε he; filter_upwards [h _ (half_pos he),h' _ (half_pos he)] with i hi hj x hx
  exact (norm_add_le ..).trans_lt ((add_lt_add (hi _ hx) (hj _ hx)).trans_eq (add_halves ε))
lemma congr {l} (h : CompactSmall l K A) (h' : ∀ᶠ i in l, K.EqOn (A i) (B i)) : CompactSmall l K B := by
  intro ε he; filter_upwards [h _ he,h'] with i hi h x hx; rw [← h hx]; exact hi x hx
lemma sum {J : Type*} (s : Finset J) {f : J → ι → Points n → M} (h : ∀ i∈s, CompactSmall l K (f i)) :
    CompactSmall l K (∑ i∈s, f i) := by
  induction s using Finset.induction_on with
  | empty=> simp only [CompactSmall,Finset.sum_empty, Pi.zero_apply,norm_zero]; exact fun ε he => Eventually.of_forall fun _ _ _ => he
  | insert i s hi ih => rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
variable [NormedSpace ℂ M]
lemma prefactor {c : ι → ℂ} {a : ℂ} (h : Tendsto c l (𝓝 a)) (hf : CompactSmall l K A) :
    CompactSmall l K (fun i x => c i • A i x) := by
  intro ε he; let t:= ‖a‖+1
  have ht : 0<t:=by unfold t; positivity
  filter_upwards [h.norm.eventually (gt_mem_nhds (lt_add_one _)), hf (ε/t) (div_pos he ht)] with i hi hf x hx
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (le_of_lt hi : ‖c i‖≤t) (norm_nonneg _)).trans_lt
    ((mul_lt_mul_of_pos_left (hf x hx) ht).trans_eq (mul_div_cancel₀ _ ht.ne'))
lemma vanishing {c : ι → ℂ} {D : Points n → M} (h : Tendsto c l (𝓝 0))
    (hc : ContinuousOn D K) (hk : IsCompact K) : CompactSmall l K (fun i x=> c i • D x) := by
  intro ε he; obtain ⟨a,ha⟩:= hk.exists_bound_of_continuousOn hc
  let t:= |a|+1; have ht : 0<t:=by unfold t; positivity
  have h₁ : Tendsto (fun i => ‖c i‖*t) l (𝓝 0) := by simpa using h.norm.mul_const t
  filter_upwards [h₁.eventually (gt_mem_nhds he)] with i hi x hx
  rw [norm_smul]; exact (mul_le_mul_of_nonneg_left ((ha x hx).trans ((le_abs_self _).trans (lt_add_one _).le)) (norm_nonneg (c i))).trans_lt hi
end CompactSmall
end extension

set_option maxHeartbeats 200000 in
lemma moving (hU : Aligned F g U) {V : ℝ→Ribbon free t} {v : Ribbon free t}
    (h : ∀ i,Tendsto (fun r => V r i) trail (𝓝 (v i)))
    (K : Set (Points n)) (hk : IsCompact K) (hV : K ⊆ conf n) :
    CompactSmall trail K (fun r x => iteratedFDeriv ℝ j (tableRead (U r) r (hang t (V r))) x -
      iteratedFDeriv ℝ j (disc (hang t v)) x) := by
  let R (b : record C t) r := tableRead (U r) r (hang t (combination _ b))
  let T (b : record C t) := disc (hang t (combination _ b))
  let w(b : record C t) r := coords _ b (V r)
  let W(b : record C t) := coords _ b v
  let I (b : record C t)(r:ℝ) (x:Points n) := w b r • (iteratedFDeriv ℝ j (R b r) x - iteratedFDeriv ℝ j (T b) x)
  let J (b : record C t)(r:ℝ) (x:Points n) := (w b r-W b) • iteratedFDeriv ℝ j (T b) x
  have hw(b:record C t) : Tendsto (w b) trail (𝓝 (W b)) := tendsto_coords _ b h
  have hh (b:record C t) : ContDiffOn ℝ j (T b) (conf n):= (smoothDisc (Free.hierarchy C.labels).smooth _).of_le (WithTop.coe_le_coe.mpr le_top)
  have ha : CompactSmall trail K ((∑ b, I b)+(∑ b, J b)) := by
    refine (CompactSmall.sum _ (fun b _ => CompactSmall.prefactor (hw b) (A:=fun r x =>
        iteratedFDeriv ℝ j (R b r) x-iteratedFDeriv ℝ j (T b) x) (fun ε he=>hU.jets _ _ _ K hk hV he))).add (CompactSmall.sum _ fun b _=> ?_)
    have hz := (hw b).sub_const (W b); rw [sub_self] at hz
    refine CompactSmall.vanishing (D:=iteratedFDeriv ℝ j (T b)) hz ?_ hk
    exact (ContinuousOn.continuousOn_iteratedFDeriv (hh b) (conf_open n) le_rfl).mono hV
  apply ha.congr; filter_upwards [show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin] with r hr
  intro x hx
  have hG(y : Points n) : tableRead (U r) r (hang t (V r)) y= ∑ b,w b r • R b r y :=
      basis_tuple _ (V r) ((S.classMoment S t (r • y)).compLinearMap (fun i => (U r (t i)).toLinearMap))
  have hF(y : Points n) : disc (hang t v) y= ∑ b,W b • T b y :=
      basis_tuple _ v ((free).classMoment free t y)
  have hR b : ContDiffAt ℝ j (R b r) x := (((smoothZoom F.room.kernel.smooth _ hr) x (hV hx)).contDiffAt
          ((conf_open _).mem_nhds (hV hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have hT b : ContDiffAt ℝ j (T b) x := ((hh b).contDiffAt ((conf_open _).mem_nhds (hV hx)))
  dsimp only
  rw [funext hG,funext hF, iteratedFDeriv_fun_sum_apply (f:=fun b y=> w b r • R b r y) (fun i _ => (hR i).const_smul _),
      iteratedFDeriv_fun_sum_apply (f:=fun b y=> W b • T b y) (fun i _ => (hT i).const_smul _), ← Finset.sum_sub_distrib]
  simp_rw [Pi.add_apply, Finset.sum_apply,← Finset.sum_add_distrib,I,J,iteratedFDeriv_const_smul_apply' (hR _),iteratedFDeriv_const_smul_apply' (hT _),smul_sub,sub_smul]
  abel_nf -- may need congr each summand
end YM.AllOrder.Leading
