import YM.FormalOPE.RG10.Profile.Relax
import Mathlib.Topology.Order.LiminfLimsup

/-! Analog of the Baire uniform boundedness estimate for two-scale Harvests. No conclusion of
uniform boundedness in the controller filter: get (possibly sequence-free) frequently along
that filter a usable Banach-Steinhaus bound uniformly over **epoch**. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Set Function Filter Metric
open scoped ContDiff Topology Classical
variable {I E : Type*}[Countable I]{L:Filter I}[NeBot L][AddCommGroup E][Module ℝ E]
    [TopologicalSpace E][ContinuousAdd E][ContinuousSMul ℝ E] (U : I → ℕ → E →L[ℝ] ℝ)

def BoundedTail (q : I) (m : ℕ) (M : ℝ) : Set E := ⋂ k:ℕ, {x | ‖U q (m+k) x‖ ≤ M}

omit [Countable I] [ContinuousAdd E] [ContinuousSMul ℝ E] in
private theorem boundedTailClosed (q : I)(m : ℕ)(M : ℝ) : IsClosed (BoundedTail U q m M) :=
    isClosed_iInter (fun k=> isClosed_le (U q (m+k)).continuous.norm continuous_const)

/-- shrinking test property, at *one controller setting* -/
def Calm (q : I) : Prop := ∀ u:ℕ→ E, Tendsto u atTop (𝓝 0)→ Tendsto (fun n=> U q n (u n)) atTop (𝓝 0)

omit [Countable I] in
private theorem calm {q:I}{m M:ℕ} (h:(interior (BoundedTail U q m M)).Nonempty) : Calm U q := by
 obtain ⟨x,hx⟩:=h; intro u hu; apply Metric.tendsto_nhds.mpr; intro ε he
 let c := (2*M+1:ℝ)/ε; have hc : 0<c:= by unfold c; positivity
 have hh : Tendsto (fun n=> x + c • u n) atTop (𝓝 x):=by simpa only [smul_zero,add_zero] using! tendsto_const_nhds.add (hu.const_smul c)
 filter_upwards [hh.eventually (isOpen_interior.mem_nhds hx), eventually_ge_atTop m] with n he' hm
 have hb {z} (hz:z∈interior (BoundedTail U q m M)) : ‖U q n z‖ ≤ M:= by
   rw [← Nat.add_sub_of_le hm]
   exact mem_iInter.mp (interior_subset hz) _
 have ht : c * ‖U q n (u n)‖ ≤ (M:ℝ) + M:=by
   rw [show c= ‖c‖ from (Real.norm_of_nonneg hc.le).symm]
   rw [← norm_smul, ← map_smul]
   rw [show U q n (c • u n)= U q n (x+c • u n)-U q n x by simp]
   exact (norm_sub_le _ _).trans (add_le_add (hb he') (hb hx))
 rw [dist_zero_right]; apply (mul_lt_mul_iff_right₀ hc).mp
 apply lt_of_le_of_lt ht; unfold c; rw [div_mul_cancel₀ _ he.ne']; linarith

variable [BaireSpace E]
theorem bargaining {T : E → ℝ} (h:∀ u, ∀ᶠ q in L, Tendsto (fun n=> U q n u) atTop (𝓝 (T u))) : ∃ᶠ q in L, Calm U q := by
 intro he
 let S : {q:I // ¬ Calm U q} × (ℕ × ℕ) → Set E:=fun p=> BoundedTail U p.1.val p.2.1 p.2.2
 have hf: (⋃ p,S p)= univ:= by
    ext x; refine ⟨fun _=> mem_univ _,fun _=>?_⟩
    obtain ⟨q,hq,hx⟩ := (he.and (h x)).exists; obtain ⟨M,hM⟩:= hx.norm.isBoundedUnder_le
    obtain ⟨m,hk⟩:= eventually_atTop.mp (show ∀ᶠ i:ℕ in atTop, ‖U q i x‖ ≤ M from hM)
    obtain ⟨N,hN⟩:= exists_nat_gt M
    exact mem_iUnion.mpr ⟨(⟨q,hq⟩,m,N),mem_iInter.mpr (fun n=> show ‖U q _ x‖ ≤ (N:ℝ) from (hk (m+n) (by omega)).trans hN.le)⟩
 obtain ⟨⟨q,m,M⟩,hw⟩:= nonempty_interior_of_iUnion_of_closed (X:=E) (fun p=> boundedTailClosed ..) hf
 exact q.2 (calm U hw)
end YM.FormalOPE.RG10.Profile
