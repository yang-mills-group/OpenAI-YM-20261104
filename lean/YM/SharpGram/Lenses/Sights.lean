import YM.SharpGram.Lenses.Mantle

/-!
# All-k moments on one measuring path

Along all k (NOT saying every length; `radius` depends on k). Compare tensors
pointwise in separated fixed compacta, with continuity at all projection ties.
Extra finite-support costs + Marshal Graded & price. Then get leading and
actual coercivity on the **point-reflected** form on the independent quotient
basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Lenses.Mantle
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open PhysicalNext.RankCovariance Org Spec Next.UVStress Further.CorrectedLift MergeProof.East Weak.Portfolio
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
variable {u:Filter (ℕ×ℕ)} (B:Mantle F u)
local notation "S'"=> (Bel C.book)
local notation "V!"=> F.sector.derivatives
local notation "V!'" => Maxwell.Free.scheme C.labels
local notation "P"=> C.path.levels.clock.hatBeta
local notation "σ"=> F.room.kernel.spin
local notation "θ"=> Maxwell.Free.spin_free C.labels

def radius k := (B.glassStation k).radius k
lemma positive k : 0 < B.radius k := Weak.Portfolio.charged ..
lemma proper : ∀ᶠ k in atTop,C.S.a k ≤ B.radius k ∧ B.radius k ≤ C.S.a k*(P k)^2 := B.prices.mono fun _ h=>⟨h.lower,h.bound⟩
lemma small : Tendsto B.radius atTop (𝓝 0) := squeeze_zero' (Eventually.of_forall fun _=>(B.positive _).le)
    (B.prices.mono (fun _ h=>h.shrink)) (cost_clears.comp B.grows)
lemma aged (D:ℕ) : ∀ᶠ k in atTop, Extra.WeakScaling.Graded V! V!' σ θ (B.lens k) D := by
  filter_upwards [B.prices,B.grows.eventually_ge_atTop D] with k hk he
  exact ⟨fun d hd=>hk.basis.1 d (hd.trans he),fun i j hij hj=>hk.basis.2 i j hij (hj.trans he)⟩
lemma pricesD (d:ℕ) : ∀ᶠ k in atTop, Costs C k d u (B.lens k d) := by
  filter_upwards [B.prices,B.grows.eventually_ge_atTop d] with i hi he
  exact hi.access ⟨d,Nat.lt_succ_of_le he⟩

variable {n : ℕ}{p : Caps n}
-- diagonal actually achieves ANY fixed test with these properties
lemma basis_fades (v : record C p) :
    let H := hang p (depthWord p v)
    Fades (fun k=> tested (B.radius k) (testLens (B.lens k)) H-disc H) := by
  intro H
  refine ⟨fun k =>(smoothZoom F.room.kernel.smooth _ (B.positive k)).sub (smoothDisc (T:=Bel C.book) (Maxwell.table_smooth _) _),fun s hs hx M _ ε he=>?_⟩
  filter_upwards [(size_ascends.comp B.grows).eventually (Work.A05.compact_fits hs hx), (cost_clears.comp B.grows).eventually (ge_mem_nhds he), (size_ascends.comp B.grows).eventually_ge_atTop M, B.grows.eventually_ge_atTop n, eventually_all.mpr (fun i=> B.grows.eventually_ge_atTop (p i)), B.prices] with k hm hK hM hd hk hP t hT hq
  exact (hP.leading.ticket hd p hk v t (hT.trans hm) (fun i=>(hq i).trans hM)).trans hK
lemma every_test (v:ℕ → Ribbon (Bel C.book) p) (x: Ribbon (Bel C.book) p)
    (hz : ∀ i, Tendsto (fun k=>v k i) atTop (𝓝 (x i))) : Fades (fun k=> tested (B.radius k) (testLens (B.lens k)) (hang p (v k)) - disc (hang p x)):=
    fadeTuple F B.positive (fun i=>B.basis_fades i) v x hz

variable {j : ℕ→ℕ} (hj:Tendsto j atTop atTop) (ha:StrictAnti (B.radius ∘ j))
def focuses : Scaling S := ⟨B.lens ∘ j,fun _=>1,B.radius ∘ j,fun _=> one_pos,fun _ => B.positive _, ha,B.small.comp hj⟩

lemma approaches : Approaches (path (B.focuses hj ha)) (isoPanel (B.focuses hj ha)) := by
  constructor; intro n v
  have he:= B.every_test (p:=fun i=>(v i).1) (fun _ i=>(v i).2) (fun i=>(v i).2) (fun _=>tendsto_const_nhds)
  exact ⟨fun k=> he.smooth _,fun s hs hS M hM ε hε=> hj.eventually (he.reads s hs hS M hM ε hε)⟩

/-- Use old Tools about stricly anti r, by paying for decay on all paths.
Thin ONLY in this predicate's proof. Don't use that as a moving-scale claim
without applying the predicate filter below. -/
lemma onFocus (V : ℕ → Prop) (hV : ∀ (j:ℕ→ℕ),Tendsto j atTop atTop → StrictAnti (B.radius ∘ j) → ∀ᶠ i in atTop,V (j i)) :
    ∀ᶠ k in atTop,V k := by
   by_contra h
   have hz : ∃ᶠ k in atTop, ¬ V k := by simpa only [Filter.Frequently, not_not] using h
   obtain ⟨n,hn⟩:=hz.exists
   have h (k:ℕ) := ((hz.and_eventually (B.small.eventually (gt_mem_nhds (B.positive k)))).and_eventually (eventually_gt_atTop k)).exists
   choose y hy hY using h
   let j (k:ℕ):ℕ:= Nat.rec n (fun _ x=>y x) k
   have he : StrictMono j := strictMono_nat_of_lt_succ (fun i=> hY (j i))
   obtain ⟨k,hk⟩:= (hV j he.tendsto_atTop (strictAnti_nat_of_succ_lt fun i=>(hy (j i)).2)).exists
   cases k
   · exact hn hk
   exact (hy _).1 hk

-- WS moments on adjusted bases. Includes all derivatives (and derivatives of true states, not the raw lattice extend).
lemma uniformJets (v:ℕ → Ribbon (Bel C.book) p) (x:Ribbon (Bel C.book) p)
    (hz : ∀ i, Tendsto (fun k=>v k i) atTop (𝓝 (x i)))
    (j : ℕ) (s : Set (Points n)) (hs : IsCompact s) (hu : s ⊆ conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ y∈s, ‖iteratedFDeriv ℝ j (tested (B.radius k) (testLens (B.lens k)) (hang p (v k))) y - iteratedFDeriv ℝ j (disc (hang p x)) y‖ ≤ ε :=
  B.onFocus _ (fun z hz' ha=> travels_jet F.room.kernel F.phase.transport.derivatives (Maxwell.Free.hierarchy _) (Maxwell.Free.scheme_derives _) (B.focuses hz' ha) (B.approaches hz' ha) (v ∘ z) x (fun i=>(hz i).comp hz') j s hs hu ε he)

lemma stable_focus : Stable σ θ V! V!' (B.focuses hj ha) := by
  constructor
  · intro d; filter_upwards [hj.eventually (B.aged d)] with i he; exact ⟨(he.1 d le_rfl).1,(he.1 d le_rfl).2.1⟩
  · intro d e h; exact hj.eventually ((B.aged e).mono fun i he=> he.2 _ e h le_rfl)
  intro d; exact hj.eventually ((B.aged d).mono fun i he => (he.1 d le_rfl).2.2)

-- export rescaled representative derivatives on all k
lemma sights (d:ℕ)(a:Axis)(v:ℕ→ (S').Field d) (x:(S').Field d)
    (h : Tendsto v atTop (𝓝 x)) : Tendsto (fun k => B.radius k • ((B.lens k (d+1)).symm ((V!).deriv d a (B.lens k d (v k))))) atTop
    (𝓝 ((V!').deriv d a x)) := by
  refine Metric.tendsto_nhds.mpr fun ε he=>B.onFocus _ fun j hj ha=>?_
  have ht:= bend_limit F.room.kernel F.phase.transport.derivatives (Maxwell.Free.hierarchy _) (Maxwell.Free.scheme_derives C.labels) (B.focuses hj ha) d a (B.approaches hj ha)
  exact Metric.tendsto_nhds.mp (Dash.arcing ht (h.comp hj)) ε he

open Push.FiniteDetection.Free

-- actual not tilted
local instance {G: Gauge} {L:Register G} (S:Table L)(d:ℕ) : FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _

def reflectAt (k d : ℕ) : RealForm ((S').Field d) ((S').Field d) := pullBoth ((B.lens k d).toLinearMap.restrictScalars ℝ) ((B.lens k d).toLinearMap.restrictScalars ℝ) (glass S σ d (B.radius k • detectors))
lemma reaches (d : ℕ) : Tendsto (fun k=>B.reflectAt k d) atTop (𝓝 (Weak.Portfolio.model C d)):=by
  apply formsLimits; intro x y
  let q : Ribbon (Bel C.book) (fun _ : Fin 2=>d):= ![x,(Bel C.book).adj θ d timeAxis y]
  let h k := tested (B.radius k) (testLens (B.lens k)) (hang _ q)
  let h0:= disc (hang _ q)
  have he:Tendsto (fun k=>h k detectors) atTop (𝓝 (h0 detectors)):=by
    rw [Metric.tendsto_nhds]; intro ε hε
    filter_upwards [B.uniformJets (fun _=>q) q (fun _=>tendsto_const_nhds) 0 {detectors} (isCompact_singleton) (singleton_subset_iff.mpr detectors_in) (ε/2) (half_pos hε)] with k hk
    have hh : ‖h k detectors - h0 detectors‖ ≤ ε/2 := by
      have hs:=hk detectors rfl
      change ‖iteratedFDeriv ℝ 0 (h k) detectors - iteratedFDeriv ℝ 0 h0 detectors‖ ≤ _ at hs
      rw [← iteratedFDeriv_sub_apply ?_ ?_, norm_iteratedFDeriv_zero] at hs; exact hs
      · exact (smoothZoom F.room.kernel.smooth _ (B.positive k) _ detectors_in |>.contDiffAt ((conf_open _).mem_nhds detectors_in)).of_le (by simp)
      exact (smoothDisc (T:= S') (Maxwell.table_smooth _) (hang _ q) _ detectors_in|>.contDiffAt ((conf_open _).mem_nhds detectors_in)).of_le (by simp)
    rw [dist_eq_norm]; exact hh.trans_lt (half_lt_self hε)
  have hh := Complex.continuous_re.continuousAt.tendsto.comp he
  refine hh.congr' ?_
  filter_upwards [B.aged d] with k ⟨ha,hh⟩
  change (S.classMoment S (fun _=>d) _ (fun i=>B.lens k d (q i))).re=glass S σ d (B.radius k • detectors) (B.lens k d x) (B.lens k d y)
  rw [glass_reads]
  congr 2
  funext i; fin_cases i
  · rfl
  have hx' (i z) : B.lens k d ((S').mirror θ d i z) = S.mirror σ d i (B.lens k d z) := (ha d le_rfl).1 ..
  change B.lens k d ((S').adj θ d timeAxis y)=S.adj σ d timeAxis (B.lens k d y)
  rw [Table.adj,Table.adj]; simp only [LinearMap.comp_apply,hx']; exact congr_arg _ ((ha d le_rfl).2.1 y)

theorem reflects (d : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop, ‖B.reflectAt k d - Weak.Portfolio.model C d‖ ≤ δ/2 ∧
    coercive (B.reflectAt k d) (δ/2) := by
  obtain ⟨δ,h,A⟩:=Weak.Portfolio.freely (C:=C) d
  refine ⟨δ,h,?_⟩
  filter_upwards [stayNear (B.reaches d) (half_pos h)] with k hk
  exact ⟨hk,absorb _ _ δ (δ/2) A (by simpa only [sub_half] using hk)⟩
end YM.SharpGram.Lenses.Mantle
