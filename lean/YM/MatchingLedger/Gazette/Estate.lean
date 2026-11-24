import YM.MatchingLedger.Gazette.Pricing
import YM.Work.F03

/-!
# Posterior precision, *prior* to actual β weighting

Invert in physical color basis on free variables. True gap independent of period. By a small real
ray in Wilson*kernel score (no selecting a PathData input). Use analytic small-field branch with
all actual tags and C1's Work.E02 coercive estimate. Keep the chart conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Gazette
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Metric Push.SectorMeasure
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side} {G : Gauge} {S : StepData c f} (F : Forest S.ratio)

section calendar

variable (s : S.Choices)
def estate (x : Chip (Meter F G)) := ∑ i, dues S F G s i x
lemma estate_exact (x : Chip (Meter F G)) : estate F s x= energy (litter F x)+S.kernel.penalty*∑ e:Bond c,G.price (venue F x e*(S.prediction (litter F x) s e)⁻¹):= total_exact S _ s _
lemma estate_nn (x : Chip (Meter F G)) : 0≤estate F s x:= total_nn (bill_nn S (litter F x) _ s)
lemma dues_analytic (z : Site c) : ContDiffAt ℝ ω (dues S F G s z) 0 := by
  obtain ⟨A,L⟩:= LocalH.actual G; let H := Classical.choice (Budget.months A L 2 (by simp))
  exact (H.duty F (show ‖(0:Chip (Meter F G))‖≤ _ from norm_zero.trans_le (H.space_pos F).le) s z).analytic
lemma estate_analytic : ContDiffAt ℝ ω (estate F (G:=G) s) 0 := ContDiffAt.sum fun i _=> dues_analytic F s i

variable (hB : S.patch.Branches S.kernel G) (z : Site c)
include hB
lemma dues_zero : dues S F G s z 0=0:= by
  unfold dues; rw [duet,litter_zero,venue_zero, show S.prediction (1 : Config G f) s =1 from funext fun i=> Push.settled S hB i s]; simp only [faceValue, show ∀ (i : Site f)(w : Walk), travel (1 : Config G f) i w=1 from fun i w=> by rw [← Precision.link_one]; exact Push.stroll_zero ..,
    Pi.one_apply,inv_one,mul_one,G.price_one,Finset.sum_const_zero, mul_zero,add_zero] -- check names
lemma dues_still : fderiv ℝ (dues S F G s z) 0=0:= IsLocalMin.fderiv_eq_zero (show IsLocalMin (dues S F G s z) 0 from by refine Filter.Eventually.of_forall fun i=>?_ ; exact (dues_zero F s hB z).trans_le (bill_nn S _ _ _ _))
lemma vacated : estate F (G:=G) s 0=0 := by unfold estate; simp_rw [dues_zero F s hB]; simp
lemma still : fderiv ℝ (estate F (G:=G) s) 0=0:=
  (show IsLocalMin (estate F (G:=G) s) 0 from Filter.Eventually.of_forall fun x=> (vacated F s hB).trans_le (estate_nn F s x)).fderiv_eq_zero
omit hB
end calendar

section precision
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E → ℝ)
def slab := fderiv ℝ (fderiv ℝ a) 0
lemma slab_two (v w:E) : iteratedFDeriv ℝ 2 a 0 ![v,w]=slab a v w:= by rw [iteratedFDeriv_two_apply]; simp [slab]
lemma slab_score (h : ContDiffAt ℝ 2 a 0)(v w:E): slab a v w=slab a w v:= h.isSymmSndFDerivAt (by simp) v w
lemma slab_ray (h : ContDiffAt ℝ 2 a 0) (he:a 0=0)(hf:fderiv ℝ a 0=0)(v:E):
    Tendsto (fun s : ℝ=> a (s • v)/s^2) (𝓝[≠] 0) (𝓝 (slab a v v/2)):=by
  rw [← slab_two,← Work.F03.line_second h hf]
  apply Work.F03.taylor_limit_two
  · exact (show ContDiffAt ℝ 2 a ((0:ℝ) • v) from by simpa using h).comp (f:=fun t:ℝ=> t • v) 0 (contDiffAt_id.smul contDiffAt_const)
  · simpa using he
  rw [(Push.side a (h.differentiableAt (by simp)) v).deriv,hf]; rfl
end precision

section denom
variable {ι α : Type} [Fintype ι] [Fintype α]

def climb : Chip ι →L[ℝ] Chip (ι ⊕ α):= ContinuousLinearMap.pi (Sum.elim (fun i=>ContinuousLinearMap.proj i) (fun _=>0))
def descend : Chip α →L[ℝ] Chip (ι ⊕ α):= ContinuousLinearMap.pi (Sum.elim (fun _=>0) (fun i=>ContinuousLinearMap.proj i))
omit [Fintype ι] [Fintype α] in
lemma summitL (x : Chip ι) : binL (α:=α) (climb x)=x:= rfl
omit [Fintype ι] [Fintype α] in
lemma summitR (x : Chip ι) : binR (α:=α) (climb x)=0:= rfl
omit [Fintype ι] [Fintype α] in
lemma pieces (x : Chip ι) (y : Chip α):
    Sum.elim x y=climb x + descend y := by ext i; cases i with
    | inl i=> exact (add_zero (x i)).symm
    | inr i=> exact (zero_add (y i)).symm
lemma link_limit (x : Chip (Kernel G ι))(i : ι) :
    Tendsto (fun t : ℝ=> G.chord (launch (t•x) i)^2 / t^2) (𝓝[≠] 0) (𝓝 (‖tint G ι x i‖^2)):= by
  let c : G.Color:= tint G ι x i; let V (t:ℝ):= launch (t • x) i
  have he (t:ℝ) : V t=G.lieExp (t • c) := by unfold V c launch; rw [map_smul]; rfl
  have ht : HasDerivAt (fun t : ℝ => G.mat (V t)) (G.colorMat c) 0 := by
    simp_rw [he,G.mat_lieExp,map_smul]
    simpa using! hasDerivAt_exp_smul_const (G.colorMat c) (0:ℝ)
  simp_rw [G.chord_price,mul_div_assoc]; exact (show Tendsto (fun t => 2*(G.price (V t)/t^2)) (𝓝[≠] 0) (𝓝 (‖c‖^2)) from by convert! (Work.F03.price_limit (V:=V) (by simp [V]) ht).const_mul (2:ℝ) using 1; ring_nf)
end denom

section gap

variable (s : S.Choices)(hB : S.patch.Branches S.kernel G)(hs : InRange S)

def basisLaw (G : Gauge) := (slab (estate (G:=G) F s)).bilinearComp climb (climb : Chip (Needle F G) →L[ℝ] Chip (Meter F G)) -- check names

-- actually invert the full *vertical* Hessian at the analytic origin
local notation "m" => lowerCost G S.patch S.kernel

include hB hs
private lemma silver (x : Chip (Meter F G))(hx : venue F x=1) {A : ChartRatio G} {n : ℕ} (H : Budget G A n)
    (hp:‖x‖≤ H.space S.patch S.kernel): m⁻¹ * (∑ i : F.Free,G.chord (launch (ι:=F.Free) (binL x) i)^2)≤ estate F s x := by
  let U:= litter F x; let V:= venue F x
  obtain ⟨t,-,ht⟩:= Finset.exists_ne_zero_of_sum_ne_zero (f:=S.likelihood U) (by rw [S.chosen hB U]; exact one_ne_zero)
  have he : estate F s x = estate F t x:= Finset.sum_congr rfl fun i _=> H.ignored F hp s t i
  rw [he]; let L:=(lowerCost G S.patch S.kernel)
  have hy : 0 < m:= zero_lt_one.trans_le (Action.lower_pos G S.patch S.kernel)
  have h0 : total Finset.univ (outside V)=0:=by unfold total outside V; rw [hx]; simp
  have hh' : SliceSet S F U:= fun i hi=> F.on_tree _ ⟨i,hi⟩
  have hv := lower Finset.univ F hh' hs (show Alive S U t from lt_of_le_of_ne (S.likelihood_pos ..) ht.symm) V
  rw [h0,sub_zero] at hv
  refine le_trans ?_ (le_trans hv (total_mono (bill_nn S U V t) (Finset.subset_univ _)))
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hy).le
  let w (i : Bond f):= G.chord (U i)^2
  change _ ≤ total _ (links S U); unfold total links; rw [total_at, loc_all]; change _ ≤ ∑ i,w i
  have hw i : Gazette.launch (ι:=F.Free) (binL x) i = U i.val := (F.off_tree _ i).symm
  simp_rw [hw]; calc
    _ = ∑ i∈ Finset.univ.filter (fun i=> i∉F.trunks),w i:= by rw [Finset.sum_subtype _ (p:=fun i=> i∉F.trunks) (by simp)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> sq_nonneg _)

lemma gold (x : Chip (Needle F G)) : m⁻¹ * (∑ i, x i ^2) ≤ basisLaw F s G x x/2 := by
  let y : Chip (Meter F G):= climb x
  have hE:= estate_analytic (G:=G) F s; let H:= estate (G:=G) F s
  have hx_:= slab_ray H (hE.of_le le_top) (vacated F s hB) (still F s hB) y
  let D:= (m)⁻¹
  have hp : (∑ i: F.Free, ‖tint G F.Free x i‖^2)= (∑ i, x i ^ 2) := vertical_count F x
  rw [← hp]; apply le_of_tendsto_of_tendsto ((tendsto_finsetSum _ (fun i _=> link_limit x i)).const_mul D) hx_
  obtain ⟨A,L⟩:= LocalH.actual G; let W:=Classical.choice (Budget.months A L 2 (by simp))
  let k:=W.space S.patch S.kernel
  have ht : ∀ᶠ t : ℝ in 𝓝 0, ‖t • y‖ ≤ k := by
    have he : Tendsto (fun t : ℝ=> t • y) (𝓝 0) (𝓝 0):= by simpa using (show Continuous fun t : ℝ=> t • y by fun_prop).tendsto 0
    filter_upwards [he.eventually (closedBall_mem_nhds (0:Chip (Meter F G)) (show 0<k from W.space_pos F))] with i hi; simpa using hi
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds] with t ht
  have hV (t:ℝ): venue F (t • y)=1:=by unfold y venue; rw [map_smul,summitR,smul_zero, runway_zero]
  rw [← Finset.sum_div, ← mul_div_assoc, ← show binL (t • y)=t • x by rw [map_smul]; rfl]; exact div_le_div_of_nonneg_right (silver F s hB hs (t • y) (hV t) W ht) (sq_nonneg _)
end gap
end YM.MatchingLedger.Gazette
