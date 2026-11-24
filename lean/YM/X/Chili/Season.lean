import YM.X.Chili.Bounty
import YM.X.Chili.Peat
/-!
# Reading a grade at any scaled tower at Taylor stage. Supports explicit shelf powers. Travel ≥ R implies Du budget grows.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark Tensor Ocean
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d:ℕ} {G:Gauge} {R T':ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable (b: Bool){X:ℕ→Okay G n}{A:ℕ→Brush G}
def cuppa (b:Bool)(A:ℕ→Brush G)(f:Fan G): Mist ℝ:= fun i z=> flatL (A i) (leadsL (pace b z) f)
lemma anim (q:Hair G)(l:Fin m→Axis): cuppa b A (jetRow m l q)= fun i z=> jumped l (raising q.1.2 (A i)) (pace b z+ q.1.1) q.2:= by funext i z; rw [cuppa,jets_lead,jets_row]; rfl
def axisP (G:Gauge)(n:ℕ)(a:Axis): Okay G n →ₗ[ℝ] T E4 G.Color n:= (LinearMap.proj a) ∘ₗ (evenShape (G:=G) n).subtype ∘ₗ (LinearMap.ker (downKG (G:=G) n)).subtype
@[simp] lemma axisP_point (p: Okay G n)(a:Axis):axisP G n a p=p.val.val a:= rfl
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 40000 in
private lemma axisP_cost (h:Released X)(a:Axis): Released (⇑(axisP G n a) ∘ X):= by
    obtain ⟨x,h⟩:=h; unfold axisP;
    have H1 : Tendsto (fun k=> (X k).val) atTop (𝓝 x.val):= (LinearMap.ker (downKG (G:=G) n)).subtypeL.continuous.continuousAt.tendsto.comp h
    have H2 : Tendsto (fun k=> (X k).val.val) atTop (𝓝 x.val.val):= (continuous_subtype_val).continuousAt.tendsto.comp H1; exact ⟨x.val.val a,tendsto_pi_nhds.mp H2 a⟩
include hq
set_option maxHeartbeats 600000 in
lemma upright (hr:0≤R)(h:Released X)(f:Fan G)(hf:f∈Reed.grads G m): Visa q R 0 ((n:ℤ)-m) (cuppa b (fun i=> launch (X i)) f):= by
    induction hf using Submodule.span_induction with
    | mem p hp=>
       obtain ⟨⟨l,p⟩,rfl⟩:=hp; unfold Function.uncurry; rw [anim]; rcases le_or_gt m n with ht|ht
       · let P:= axisP G n p.1.2; rw [show ((n:ℤ)-m)=↑(n-m) from by omega]; let F : ℕ→ T E4 G.Color n:=fun i=>P (X i); have he:= axisP_cost h p.1.2; simp_rw [launch,eg]; refine (burst_result (V:=G.Color) (P:= F) hq b hr ht l (Reed.tip p.1.2) p.1.1 he (fun i=> by exact ((X i).val.sym p.1.2))).mapL (EuclideanSpace.proj p.2) -- defeq?
       simp_rw [show ∀ i:ℕ,jumped l (raising p.1.2 (launch (X i)))=0 from fun i=> larger (X i).val _ ht l]; exact Visa.zero
    | zero=> unfold cuppa; simp only [map_zero]; exact Visa.zero
    | add a c ht hk x y=> unfold cuppa; simp only [map_add]; exact x.add y
    | smul a i _ h=> unfold cuppa; simp only [map_smul]; exact h.smult a
lemma footprint_field (hr:0≤R)(he:R≤T')(h:Tide q T' A)(f:Fan G)(hf:f∈Reed.grads G m): Visa q R ((m+1:ℕ):ℤ) 0 (cuppa b A f):= by
   refine ⟨?_,fun x hx hy z hz=>?_⟩
   · obtain ⟨C,hc,ht⟩:= h.amounts m f hf; refine ⟨C,hc,?_⟩; filter_upwards [ht] with i hi z hz; have hk:= hi (pace b z) ((road_pace b z).trans (hz.trans (Nat.floor_le_floor (mul_le_mul_of_nonneg_left he (amp_pos ..|>.le))))) ; simpa only [price,cuppa,zpow_natCast,zpow_zero,pow_zero,mul_one,Real.norm_of_nonneg (pow_nonneg (epsilon_pos q _|>.le) _)] using hk
   have hx' := pace_shift hq b hz 0; simp only [add_zero] at hx'; simp only [price,cuppa,zero_sub, zpow_neg,zpow_natCast, smul_eq_mul]; exact h.later m f hf (pacer b x) ((pace_norm b x).trans (hy.trans he)) _ hx'
lemma correction_street {S:ℕ→ℝ}(hr:0≤R)(he:R<T')(h:Bark (gate q T') S m k A)(f:Fan G)(hf:f∈Reed.grads G m): OnStreet (gate q R) S k (cuppa b A f):= by
   induction hf using Submodule.span_induction with
   | mem p hp=> obtain ⟨⟨l,p⟩,rfl⟩:=hp; unfold Function.uncurry; rw [anim]; obtain ⟨C,hc,hh⟩:= OnStreet.at_pos hq b p.1.1 hr he (h p.1.2 l); exact ⟨C,hc,hh.mono (fun i hi z hz=>le_trans (PiLp.norm_apply_le _ _) (hi _ hz))⟩ -- parser
   | zero=> unfold cuppa; simp only [map_zero];exact Reed.OnStreet.zero
   | add a c ht hk x y=> unfold cuppa; simp only [map_add]; exact Reed.OnStreet.add x y
   | smul a i _ h=> obtain ⟨C,hc,he⟩:= h; refine ⟨‖a‖*C,by positivity,?_⟩; filter_upwards [he] with t ht z hz; unfold cuppa; rw [map_smul,map_smul,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (ht _ hz) (norm_nonneg _)
omit hq
lemma footprint_proj (p:Fan G)(j:ℕ): leaf (vapor G) (j+1) (trumpet (Okay G) (valP (G:=G)) d (glyph (Stems.com p)))= if j<d then towerP (Okay G) valP j p else 0:= by
    rw [tru,bunch]; unfold leaf; rw [map_sum]
    have he (k:ℕ) : weightedHomogeneousComponent (vapor G) (j+1) (towerP (Okay G) (valP (G:=G)) k p)=if k=j then towerP (Okay G) (valP (G:=G)) k p else 0:= by
       split; next h=> subst k; exact (owngear j p).weightedHomogeneousComponent_same
       next h=> exact (owngear k p).weightedHomogeneousComponent_ne _ (by omega)
    simp_rw [he,Finset.sum_ite_eq',Finset.mem_range]
lemma footprint₀ (p:Fan G) : leaf (vapor G) 0 (trumpet (Okay G) (valP (G:=G)) d (glyph (Stems.com p)))=0:= by rw [tru,bunch]; unfold leaf; rw [map_sum]; exact sum_eq_zero fun i _=> (owngear i p).weightedHomogeneousComponent_ne _ (by omega)
lemma shadow_foot (p:Fan G): bloom d (glyph (Stems.com p))= trumpet (Okay G) valP d (glyph (Stems.com p)):= by
   let u:= glyph (com p); change level _ _ _=_; simp_rw [AlgHom.toLinearMap_apply,tru,bunch]; rw [map_sum]; refine Finset.sum_congr rfl fun i hi=> trimmer_hom (Finset.mem_range.mp hi) (owngear i p)
lemma expel (d:ℕ)(f:Long G)(p:Fan G) : probeL f (bloom d (glyph (com p)))= (↑(flatL (arm d f) p):ℂ):= by rw [shadow_foot,tone]; simp_rw [lif, ← arm_point]; rw [com_text,snaps_blade];rfl
end YM.PositionX.Clove
