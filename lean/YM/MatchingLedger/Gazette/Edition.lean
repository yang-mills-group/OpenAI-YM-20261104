import YM.MatchingLedger.Gazette.Estate
import YM.MatchingLedger.Books.Payment

/-!
# Coefficient program, finite-volume top transfer

A minimal step currency on physical slice, suitable also with higher horizon prices for joint
fields. Keep shell expression separately from its full-length reading in formal saddles. No
fitting: Taylor at trivial independent angles/coupling and actual score/Haar, evaluating at
external scaled log coordinates, subtracting the *nonconstant* log of Jacobian. Beta argument
strictly outside these functions. Horizon-independent definition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Gazette
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Metric Push.SectorMeasure Books MvPolynomial
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side} {G : Gauge} {S : StepData c f} (F : Forest S.ratio) (s : S.Choices)
    (A : ChartRatio G)

section price
variable {ι α : Type} [Fintype ι] [DecidableEq ι]
lemma packet_plan (v : Chip ι → ℝ) (k : ℕ) (w : Chip ι → ℝ) (he:v=ᶠ[𝓝 0] w) : packet v k=packet w k:= by unfold packet; rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
lemma packet_sum (v : α → Chip ι → ℝ) (q : Finset α) (k : ℕ) (he:∀ i∈q,ContDiffAt ℝ k (v i) 0) :
    packet (fun x=>∑ i∈q,v i x) k=∑ i∈q, packet (v i) k:=by
  apply MvPolynomial.funext; intro x
  simp_rw [← read_apply,_root_.map_sum,packet_read, YM.PertExtension.Series.Radial.jet]
  rw [← Finset.mul_sum]; congr 1
  rw [iteratedFDeriv_fun_sum_apply (f:=v) he]
  exact sum_apply ..
lemma packet_zero (v : Chip ι → ℝ) : packet v 0=C (v 0):= by apply MvPolynomial.funext; intro x; simp_rw [← read_apply,packet_read,read_C]; simp
end price

-- Joint unscaled

def print (v : Site c → Chip (Meter F G) → ℝ)(k : ℕ) : Poly (Meter F G):= ∑ z, packet (v z) k

def tip (k : ℕ) : Poly (Meter F G):= print F (dues S F G s) k
def flow (k : ℕ) : Poly (Meter F G):= print F (salary F A) k

def wide : ℕ → Poly (Meter F G)
 | 0=> tip (G:=G) F s 2
 | k+1=> tip F s (k+1+2)- flow F A (k+1)

def edition (y : Chip (Page G c)) (k : ℕ) : Poly (Needle F G) := install y (wide F s A k)

lemma salary_analytic (L : LocalRatio A) (z : Site c) : ContDiffAt ℝ ω (salary F A z) 0 := by
  let H:=Classical.choice (Budget.months A L 2 (by simp))
  exact (H.issued F (show ‖(0:Chip (Meter F G))‖≤ _ from norm_zero.trans_le (H.space_pos F).le) z).analytic

lemma tip_expr (k : ℕ) : packet (estate F (G:=G) s) k=tip F s k:= packet_sum _ _ _ (fun i _=> (dues_analytic F s i).of_le le_top)
lemma flow_expr (L : LocalRatio A)(k : ℕ) : packet (editorial F A) k=flow F A k:= by rw [show editorial F A = (fun x=> total Finset.univ (fun z=> salary F A z x)) from _root_.funext (edit F A)]; exact packet_sum _ _ _ (fun i _=> (salary_analytic F A L i).of_le le_top)
lemma flow_nil (L : LocalRatio A) : flow F A 0=0:= by rw [← flow_expr F A L, packet_zero]; simp [editorial,jac,L.anchored]
lemma edition_zero (y : Chip (Page G c)) : edition F s A y 0= install y (packet (estate F s) 2):= by rw [tip_expr]; rfl

-- test pullback same prescription. Does NOT require that cutoffs or tree bodies at two periods
-- use the same theta values here.
lemma tagless (t : S.Choices)(k : ℕ) : tip F (G:=G) s k=tip F t k:=by
  obtain ⟨A,L⟩:= LocalH.actual G; let H:=Classical.choice (Budget.months A L 2 (by simp))
  apply Finset.sum_congr rfl; intro i _; apply packet_plan
  filter_upwards [closedBall_mem_nhds (0:Chip (Meter F G)) (H.space_pos F)] with x hx; exact H.ignored F (by simpa using hx) s t i
lemma edition_tags (t : S.Choices)(Y : Chip (Page G c)) : edition F s A Y=edition F t A Y:=by
  ext1 i; unfold edition; apply congr_arg; cases i <;> (simp only [wide,tagless F s t])

-- 'print' functions from arbitrary sectors; crucially compare exact rest weights for physical estimates
section packetPrice

variable (v : Site c → Chip (Meter F G) → ℝ) {k n : ℕ} {M:ℝ}
    (he : ∀ z:Site c, Restricted (v z) (seats F z)) (hv : ∀ z:Site c, Allows n (v z) 0 M) (hk : k≤n)

local notation "J" => Action.belt S.patch

abbrev stretch (P : Patch) := Action.belt P + Action.belt P
-- finset of contributing sites and deterministic log access footprint
def depot (i : Meter F G) := halo J {atlas F i}
def arc (i : Meter F G) := halo (stretch S.patch) {atlas F i}
def ports (i : Meter F G) := located (atlas (G:=G) F) (arc F i)

lemma into (i : Meter F G) (z : Site c): i ∈ seats F z ↔ z∈depot F i:= by unfold seats ribbon depot; rw [loc,near_root,near_root,separation_comm]
lemma band (i : Meter F G) (z : Site c)(h:z∈depot F i): seats (G:=G) F z⊆ ports F i:= fun _ hj=> loc.mpr (accumulate {atlas F i} J J h (near_root.mp (loc.mp hj)))

lemma arc_mem (i : Meter F G) : i ∈ ports F i := by unfold ports; rw [loc, arc, near_root]; simp

include he hv

lemma clip_indices (i : Meter F G) : pderiv i (print F v k)=∑ z∈depot F i, pderiv i (packet (v z) k) := by
  unfold print; rw [_root_.map_sum]; refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro z _ hz; apply pderiv_eq_zero_of_notMem_vars; intro hf; exact hz ((into F i z).mp (packet_vars (he z) ((hv z).analytic.of_le le_top) hf)) -- omit hk
lemma press_vars (i : Meter F G) : (pderiv i (print F v k)).vars ⊆ ports F i := by
  rw [clip_indices F v he hv]; refine Finset.Subset.trans (vars_sum_subset ..) (Finset.biUnion_subset.mpr (fun z hz=>?_)); exact (gradient_local ..).trans ((packet_vars (he z) ((hv z).analytic.of_le le_top)).trans (band F i z hz))

def placeFare (G : Gauge)(P : Patch)(M : ℝ)(k : ℕ) := M*(bench G P (Action.belt P):ℝ)^k
omit he in
lemma placeFare_nn (z : Site c) : 0≤placeFare G S.patch M k := by unfold placeFare; positivity [(hv z).nonneg]
def gradientBill (G : Gauge)(P : Patch)(M : ℝ)(k : ℕ) := park (Action.belt P)* (k * placeFare G P M k)
omit he in
lemma gradient_nn (z : Site c) : 0 ≤ gradientBill G S.patch M k:=by unfold gradientBill; positivity [park_nn (Action.belt S.patch),placeFare_nn (k:=k) F v hv z]
include hk
lemma localFare (z:Site c) : fare (packet (v z) k) ≤ placeFare G S.patch M k :=
    (packet_cost (he z) ((hv z).analytic.of_le le_top) M ((hv z).norm_le _ hk)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (bench_le F z)) _) (hv z).nonneg)
lemma local_deriv (z : Site c) (i:Meter F G) :
    fare (pderiv i (packet (v z) k)) ≤ k * placeFare G S.patch M k:=
  (fare_gradient _ (packet_degree ..)).trans (mul_le_mul_of_nonneg_left (localFare F v he hv hk z) (Nat.cast_nonneg _))
lemma press_fare (i : Meter F G) : fare (pderiv i (print F v k)) ≤ gradientBill G S.patch M k:= by
  rw [clip_indices F v he hv]; apply (fare_sum ..).trans
  refine (Finset.sum_le_sum (g:=fun _=> k * placeFare G S.patch M k) (fun z _=>local_deriv F v he hv hk z i)).trans ?_
  rw [Finset.sum_const,nsmul_eq_mul]; unfold gradientBill; exact mul_le_mul_of_nonneg_right (by unfold park; exact_mod_cast (mag (atlas F i) J)) (mul_nonneg (Nat.cast_nonneg _) (placeFare_nn F v hv 0)) -- cast fix
omit he hv hk in
lemma press_degree (i : Meter F G) (k : ℕ) : (pderiv i (print F v k)).totalDegree ≤ k-1:= total_gradient _ (totalDegree_finsetSum_le (fun _ _=>packet_degree ..))

end packetPrice

section pay
variable {A} {n : ℕ} (H : Budget G A n) (hB : S.patch.Branches S.kernel G) {k : ℕ} (hk : k≤n)
local notation "M" => H.income S.patch S.kernel
local notation "cost" => gradientBill G S.patch M
local notation "L" => Needle F G
local notation "ω'" => Page G c

variable (i : Meter F G)
structure GradientTicket (G:Gauge) {c f:Side}(S : StepData c f)(F : Forest S.ratio)(p : Poly (Meter F G))(i : Meter F G)(k : ℕ)(W : ℝ) : Prop where
  degree : (pderiv i p).totalDegree ≤ k-1
  receipt : fare (pderiv i p) ≤ gradientBill G S.patch W k
  port : (pderiv i p).vars⊆ ports F i

theorem print_ticket (v : Site c → Chip (Meter F G) → ℝ) (he : ∀ z:Site c, Restricted (v z) (seats F z)) (hv : ∀ z:Site c, Allows n (v z) 0 M) (h:k≤n) :
    GradientTicket G S F (print F v k) i k M:= ⟨press_degree F v i k, press_fare F v he hv h i, press_vars F v he hv i⟩

lemma issued_script : ‖(0:Chip (Meter F G))‖≤ H.space S.patch S.kernel:=norm_zero.trans_le (H.space_pos F).le
include hB hk

lemma tip_paid : GradientTicket G S F (tip F s k) i k M:= print_ticket F H i _ (dues_port S F hB s) (H.duty F (issued_script F H) s) hk
omit hB in
lemma flow_paid : GradientTicket G S F (flow F A k) i k M:= print_ticket F H i _ (salary_port F A) (H.issued F (issued_script F H)) hk
omit hk hB

include hB in
lemma tip_zero_use : tip (G:=G) F s 0=0 := by rw [← tip_expr, packet_zero,vacated F s hB,_root_.map_zero]
-- charge already installed sym, include logical-ticket proof support cast. h ext max uniform
variable (Y : Chip (Page G c))
structure Value (i : Needle F G)(p:Poly (Needle F G))(d : ℕ)(v : ℝ) : Prop where
  degree : p.totalDegree≤ d
  limit : fare p ≤ v
  port : ∀ j ∈ p.vars, Sum.inl j ∈ ports F (Sum.inl i) -- need G infer


lemma Ticket {p : Poly (Meter F G)} (j : Needle F G) (T : GradientTicket G S F p (.inl j) k M) {Z : ℝ} (hZ : 1≤Z) (he: ‖Y‖≤ Z):
    Value F j (pderiv j (install Y p)) (k-1) (cost k*Z^(k-1)):=by
  rw [install_gradient]; refine ⟨(install_degree ..).trans T.degree, (install_cost Y _ Z hZ _ T.degree fun i _=>(norm_le_pi_norm _ _).trans he).trans (mul_le_mul_of_nonneg_right T.receipt (pow_nonneg (zero_le_one.trans hZ) _)), ?_⟩
  let s:= ports (G:=G) F (Sum.inl j)
  let a:=Finset.univ.filter (fun i=> Sum.inl i∈s)
  intro i hi
  exact (Finset.mem_filter.mp (install_loc Y _ a (fun i h=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,T.port h⟩) hi)).2 -- check F implicit measure

end pay
end YM.MatchingLedger.Gazette
