import YM.FrontierTrace.Primary.PoleMeter
import YM.Push.STRESS_FLUX.Matching
import YM.OPE.Cards.Pressure

/-!
# Integrated last-shell coupons, using ceil at *fine* centers on a slide shape

Generic volume (avoids projection ties a.e.). Compact smear of ANY singular measure
with this scope. Period tail chosen by f.per first, then f.mesh; ℓ and radius
FIXED throughout both. No rate assumed/claimed in this junction or illegal subsequence
shrinking common f. Calibrated MOMENTS from the exact true law; expansion in `Tracing`.
Push.STRESS_FLUX.Matching for useful generic & rulers. `radiant'` later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace.Primary.Junction
open Function Set Filter Analysis Table Work.A01 Work.A05 MeasureTheory StressFlux.Matching
open Extraction Lattice Cells Wilson Metric
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval Classical
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Spec.Final C f S)
local notation "B"=> C.book
variable {E: Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] {μ:Measure E} {n:ℕ}

lemma read_point (hx:f.PointLimits C S) (v : Fin n → (B).Token) (x : Points n) (he : x∈ generic n) : Tendsto
    (fun z:ℕ×ℕ=>C.numeric z.1 z.2 v (fun i=> ceilSite C z.1 z.2 (x i))) f.fuse (𝓝 (S.read x v)):= rounded_tendsto hx v x he

lemma ready_turn (N p:ℕ) (q: Fin n→ (B).Token) : Measurable (fun x:Points n=> (rounded C N p).read x q):=by
    change Measurable (lifted C N p q ∘ address (C.S.a N)); apply (measurable_of_countable _).comp
    exact measurable_pi_lambda _ (fun i=> measurable_pi_lambda _ (fun a=> Int.measurable_ceil.comp (by fun_prop : Measurable fun x:Points n=> x i a / C.S.a N)))
lemma finite_read (N p:ℕ) (q: Fin n→ (B).Token) :∃ D:ℝ, 0≤D ∧ ∀ x:Points n, ‖(rounded C N p).read x q‖ ≤ D:=by
    obtain ⟨d,hd⟩:= (finite_range (fun r:Fin n→ Site _=> ‖C.numeric N p q r‖)).bddAbove; refine ⟨max 0 d,le_max_left ..,fun z=> (hd (mem_range_self ( fun i:Fin n=>ceilSite C N p (z i)))).trans (le_max_right ..)⟩
omit [TopologicalSpace E] [BorelSpace E] in
lemma ready_to_use (q: Fin n→ (B).Token)(L:E→Points n)(φ:E→ℂ)
    (hL:Measurable L) (hs:Integrable φ μ) (N p:ℕ) : Integrable (fun v=>φ v * (rounded C N p).read (L v) q) μ:=by
    obtain ⟨D,hD,H⟩:=finite_read N p q
    exact (hs.norm.mul_const D).mono' (hs.aestronglyMeasurable.mul (((ready_turn N p q).comp hL).aestronglyMeasurable)) (Eventually.of_forall fun z=>
      (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (H _) (norm_nonneg _)))

-- AE pullback in both countable limits individually. Use large period and compact
-- cut k; includes projection ties but NO coincident paths. No quantitative claims.
include F
theorem junction_tail {K : Set E}(q: Fin n→ (B).Token)(L:E→Points n)(φ:E→ℂ)
    (h:Wcmain C)(hL:Continuous L)(hK:IsCompact K)(hS:∀ x∈K,L x∈conf n)
    (hw:∀ᵐ x ∂μ,x∈K)(hx:∀ᵐ x ∂μ,L x∈ generic n)(hg:Integrable φ μ) :
    ∃ pred:ℕ→Prop, f.limits pred (fun N p=>∫ x,φ x * (rounded C N p).read (L x) q ∂μ) (∫ x,φ x * S.read (L x) q ∂μ):=by
   let M:=S; have hB:= Extraction.Around.size_done F.room.cutoff (((Wcmain.projects C f F.room.cutoff h)).book _ _); obtain ⟨P,hP,hF⟩:= F.room.generic
   let U:= L '' K; let X(t:ℝ):= cthickening t U
   have hc:= hK.image hL; obtain ⟨t,ht,htK⟩ := hc.exists_cthickening_subset_open (conf_open n) (image_subset_iff.mpr hS)
   have he(k) (ha:k∈K):L k∈X t:=mem_cthickening_of_dist_le _ _ _ U (mem_image_of_mem L ha) (by simpa using! ht.le)
   have ha:IsCompact (X t):=hc.cthickening
   let W(p:ℕ)(x:E):= φ x * (P p).read (L x) q
   let V(N p:ℕ)(x:E):= φ x * (rounded C N p).read (L x) q
   have hm(p:ℕ)(hp:X t ⊆ Inside C.S p n):∀ᵐ x ∂ μ, Tendsto (fun i=> V (f.mesh i) p x) atTop (𝓝 (W p x)):= by
      filter_upwards [hw,hx] with x hx hg; exact
        (f.evaluated C hP p n q (L x) ((no_wrap_tie C.S (hp (he x hx))).mpr hg) (fun j=> address (C.S.a (f.mesh j)) (L x)) ((chosen _).comp f.mesh.cofinal)).const_mul _
   have h₁ : ∀ᶠ i:ℕ in atTop,∀ y∈U, tag (C.S.a (f.mesh i)) (address (C.S.a (f.mesh i)) y) ∈ X t:=by
      let m(i:ℕ):= (4*n:ℝ)*C.S.a (f.mesh i)
      have hm: Tendsto m atTop (𝓝 0):= by simpa only [m,mul_zero] using! ((C.S.shrinks.comp f.mesh.cofinal).const_mul (4*n:ℝ))
      filter_upwards [hm.eventually (ge_mem_nhds ht)] with i hi y hy; exact mem_cthickening_of_dist_le _ y _ U hy ((approximate (C.S.a_pos _) y).trans hi)
   have h₂ (D:ℝ) (i p:ℕ)(hs:∀ b,tag (C.S.a (f.mesh i)) b∈X t→ ‖lifted C (f.mesh i) p q b‖≤D)
     (hT:∀ y∈U,tag (C.S.a (f.mesh i)) (address (C.S.a (f.mesh i)) y)∈X t):∀ᵐ x ∂μ, ‖V (f.mesh i) p x‖≤ ‖φ x‖*D:= by
      filter_upwards [hw] with x hx; exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (hs _ (hT (L x) (mem_image_of_mem L hx))) (norm_nonneg _))
   refine ⟨fun p=> X t⊆Inside C.S p n,f.per.cofinal.eventually (room C.S ha),fun p=> ∫ x, W p x ∂μ,fun p hp=> ?_,?_⟩
   · obtain ⟨D,hD,H⟩:= hB.cyclic n q p (X t) ha (fun z hz=> (no_wrap_hit C.S (hp hz)).mpr (htK hz))
     exact tendsto_integral_filter_of_dominated_convergence (fun x=> ‖φ x‖*D) (Eventually.of_forall fun i=>
       (ready_to_use q L φ hL.measurable hg _ p).aestronglyMeasurable) ((H.and h₁).mono fun i hh=>h₂ D i p hh.1 hh.2) (hg.norm.mul_const _) (hm p hp)
   obtain ⟨D,hD,H⟩:= hB.volume n q (X t) ha htK
   have hl :∀ᵐ x ∂μ, Tendsto (fun j=> W (f.per j) x) atTop (𝓝 (φ x * S.read (L x) q)):= by
      filter_upwards [hx] with x hx; apply Filter.Tendsto.const_mul; apply Metric.tendsto_nhds.mpr
      intro ε hε; filter_upwards [hF n {(L x)} isCompact_singleton (singleton_subset_iff.mpr hx) q ε hε] with i hi; simpa only [dist_eq_norm] using (hi (L x) rfl)
   apply tendsto_integral_filter_of_dominated_convergence (fun x=>‖φ x‖*D) _ _ (hg.norm.mul_const D) hl
   · filter_upwards [f.per.cofinal.eventually (room C.S ha)] with i hi
     exact aestronglyMeasurable_of_tendsto_ae atTop (fun j=> (ready_to_use q L φ hL.measurable hg _ (f.per i)).aestronglyMeasurable) (hm (f.per i) hi)
   filter_upwards [f.per.cofinal.eventually (room C.S ha),H] with i hi heN
   have h:∀ᶠ j in atTop,∀ᵐ x ∂μ, ‖V (f.mesh j) (f.per i) x‖ ≤ ‖φ x‖ *D := (heN.and h₁).mono fun j hh=>h₂ D j _ hh.1 hh.2
   obtain ⟨j,hj⟩ := eventually_atTop.mp h
   have hv : ∀ᵐ x ∂μ, ∀ k≥j, ‖V (f.mesh k) (f.per i) x‖ ≤ ‖φ x‖*D := ae_all_iff.mpr fun k=> ae_all_iff.mpr (fun hk=>hj k hk)
   filter_upwards [hm (f.per i) hi,hv] with x ht he; exact le_of_tendsto ht.norm (eventually_atTop.mpr ⟨j,he⟩)

/- fixed-last receipts -- basis expansion of moving readout coefficients.
Moment includes all unit insertions. No center smearing exceptions. Uses EXACT
 S and unit_label. No assertion P-matrix entries stay bounded above/below along
 r→0; rate consumer cancels them. -/
section basis
variable {d: Caps n}
local notation "V"=> C.book.Vector d
local notation "E₀"=> dial (L:=C.book) d
private abbrev J₀ (C:Family G){n:ℕ}(d:Caps n) := (i:Fin n)→ (C.book.coord (d i)).Index
private def Y₀ (r:J₀ C d) (i:Fin n):= E₀ i (r i)
private def W₀ (v:V)(r:J₀ C d):= ∏ i,(E₀ i).repr (v i) (r i)
omit F in
private lemma representation (M:Moment C.book n d)(v:V): M v=∑ j:J₀ C d,W₀ v j*M (Y₀ j):=by
       have hx:v= fun i=> ∑ k,(E₀ i).repr (v i) k • E₀ i k:= funext fun i=> ((E₀ i).sum_repr _).symm
       conv_lhs=> rw [hx];
       rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl (fun j _=> M.map_smul_univ (fun k=>(E₀ k).repr (v k) (j k)) _)
omit F in
private lemma motion (t:J₀ C d) {v:V}{w:ℕ×ℕ→V}(hp:∀ i,Tendsto (fun y=>w y i) f.fuse (𝓝 (v i))): Tendsto (fun i:ℕ×ℕ=> W₀ (w i) t) f.fuse (𝓝 (W₀ v t)):=tendsto_finsetProd _ (fun k _=> ((E₀ k).coord (t k)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hp k))
lemma leg_tendsto (x:Points n)(hx:x∈generic n){v:V}{w:ℕ×ℕ→V}(hp:∀ i,Tendsto (fun y=>w y i) f.fuse (𝓝 (v i))): Tendsto
    (fun i:ℕ×ℕ=>(rounded C i.1 i.2).value d x (w i)) f.fuse (𝓝 (S.value d x v)) := by
    have hS(t:J₀ C d): Tendsto (fun i:ℕ×ℕ=> (rounded C i.1 i.2).value d x (Y₀ t)) f.fuse (𝓝 (S.value d x (Y₀ t))) := rounded_tendsto F.room.generic (fun i=>⟨d i,Y₀ t i⟩) x hx
    rw [representation (C:=C) (S.value ..) v];
    exact (tendsto_finsetSum Finset.univ (fun i _=> (motion i hp).mul (hS i))).congr' (Eventually.of_forall fun i=> (representation (C:=C) ((rounded C i.1 i.2).value d x) (w i)).symm)
lemma junction_int {K:Set E}(L:E→ Points n)(hL:Continuous L)(φ:E→ℂ)(hg:Integrable φ μ)
   (hK:IsCompact K)(hs:∀ x∈K,L x∈conf n)(hw:∀ᵐ x ∂μ,x∈K) (v:V): Integrable (fun x=>φ x*S.value d (L x) v) μ:=by
    let X : E→ℂ:= fun x=> S.value d (L x) v
    have hc: ContinuousOn X K:= ((S.smooth_read F.room.kernel.smooth (fun i=>⟨d i,v i⟩)).continuousOn.comp hL.continuousOn (fun x hx=> hs _ hx))
    obtain ⟨A,hA⟩:= (hK.image_of_continuousOn hc.norm).bddAbove
    refine (hg.norm.mul_const A).mono' ?_ (hw.mono fun x hx=> (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (hA (mem_image_of_mem (fun x=>‖X x‖) hx)) (norm_nonneg _)))
    -- `K` is compact. measurability via restrict. no volume exceptional issue.
    let Q:= L ⁻¹' (conf n); have ho:= (conf_open n).preimage hL
    have hi: ContinuousOn X Q := (S.smooth_read F.room.kernel.smooth (fun i=> ⟨d i,v i⟩)).continuousOn.comp hL.continuousOn (fun x hx=>hx)
    apply hg.aestronglyMeasurable.mul
    have hj := hi.aestronglyMeasurable (μ:=μ) ho.measurableSet; rw [Measure.restrict_eq_self_of_ae_mem (s:=Q) (hw.mono fun x h=>hs x h)] at hj; exact hj

set_option maxHeartbeats 1000000 in
theorem junction {K : Set E}(L:E→Points n)(φ:E→ℂ)(v:V)(w:ℕ×ℕ→ V)
    (h:Wcmain C)(hL:Continuous L)(hK:IsCompact K)(hS:∀ x∈K,L x∈conf n)
    (hw:∀ᵐ x ∂μ,x∈K)(hx:∀ᵐ x ∂μ,L x∈ generic n)(hg:Integrable φ μ)(hp:∀ i,Tendsto (fun y=>w y i) f.fuse (𝓝 (v i))) :
    Tendsto (fun i:ℕ×ℕ => ∫ x, φ x* (rounded C i.1 i.2).value d (L x) (w i) ∂μ) f.fuse (𝓝 (∫ x,φ x* S.value d (L x) v ∂μ)) := by
   let Z (S:Table C.book)(v:V):= ∫ x,φ x * S.value d (L x) v ∂μ
   have he(S:Table C.book)(v:V)(ht:∀ i:J₀ C d,Integrable (fun x=>φ x*S.value d (L x) (Y₀ i)) μ): Z S v=∑ j:J₀ C d,W₀ v j*Z S (Y₀ j):=by
      unfold Z; conv_lhs=> enter [2,x,2]; rw [representation (C:=C) (S.value ..) v]
      simp_rw [Finset.mul_sum,← integral_const_mul (W₀ v _), mul_left_comm (φ _) (W₀ v _)]
      rw [integral_finsetSum _ (fun i _=> (ht i).const_mul (W₀ v i))]
   have hZ(i:J₀ C d): Tendsto (fun y:ℕ×ℕ=>Z (rounded C y.1 y.2) (Y₀ i)) f.fuse (𝓝 (Z S (Y₀ i))) := Extraction.Order.along ((junction_tail F (fun j=>⟨d j,Y₀ i j⟩) L φ h hL hK hS hw hx hg).choose_spec)
   change Tendsto _ _ (𝓝 (Z S v))
   rw [he S v (fun i=> junction_int F L hL φ hg hK hS hw (Y₀ i))]
   exact (tendsto_finsetSum _ (fun i (hi:i∈(Finset.univ:Finset (J₀ C d)))=> (motion i hp).mul (hZ i))).congr' (Eventually.of_forall fun i=> (he (rounded C i.1 i.2) (w i) (fun v=> ready_to_use (fun j=>⟨d j,Y₀ v j⟩) L φ hL.measurable hg i.1 i.2)).symm)
end basis
end YM.FrontierTrace.Primary.Junction
