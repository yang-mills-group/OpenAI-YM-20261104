import YM.SharpGram.Annulus.Glass
import YM.Pier.Lair.Stream

/-! moving frame read: all fields, at true β after Limit.S.same and not translating tests after Hessian bounds. Throughout this series `Present` is already chosen; no uniqueness. induced capture norm for BOTH input and output response; proof from journey estimates plus genuine adaptive coercive TWO node reflected Gram. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Lair
open Function Filter Set Table Extraction Climb Analysis Ward Spec
open Trace Trace.Over Trace.Terrace Trace.Pilot MergeProof.East Next.Rank
open Next.UVStress Spin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{f : Extraction.Order}{S:Table C.book}
variable (F: Final C f S) (h:G.Simple) {H : (Bel C.book).Hierarchy}
set_option quotPrecheck false
local notation "B" => (Bel C.book)
local notation "θ" => Maxwell.Free.spin_free C.labels
local notation "τ" => (turns C)
local notation "W₀" => (Maxwell.Free.scheme C.book.grid)
local notation "W₁" => F.sector.derivatives
local notation "H₀" => Maxwell.Free.hierarchy C.labels
local notation "H₁" => F.room.kernel
local notation "τ₁" => F.sector.turns
variable {X:Scaling S}{l: Ultrafilter (ℕ×ℕ)}{Z:Arch C}{V:∀ i, Vane C i}
open MeasureTheory SharpGram Lenses
open scoped ContDiff

variable {Y:ℝ→FamilyBasis (C:=C) S} (P:Present F Y) (d:ℕ)
open Weak.Portfolio OPE.Levy Push.FiniteDetection.Free
local notation "D₂"=> detectors
local notation "W₂"=>Pilot.trail
local notation "U!"=> (glass (Bel C.book) θ d)
local notation "K!"=> (glass S (H₁).spin d)
local instance (V:Gauge)(T:Register V)(L:Table T)(d:ℕ): FiniteDimensional ℝ (L.Field d) := Module.Finite.trans ℂ _

def arcPrice (Z:Spin.change S d) (x:Points 2): RealForm ((B).Field d) ((B).Field d) := pullBoth (Z.toLinearMap.restrictScalars ℝ) (Z.toLinearMap.restrictScalars ℝ) (K! x)
lemma echo (x₀ x₁:(B).Field d) (X:Spin.change S d) (he:AlignO F.sector (H₁).spin (H₀) d X) (s:Points 2):
    arcPrice F d X s x₀ x₁=(S.classMoment S (fun _=>d) s (fun i=>X ((![x₀,(Bel C.book).adj θ d timeAxis x₁]: Fin 2→(Bel C.book).Field d) i))).re:=by
   let A:= Maxwell.Free.gear_laws C.labels
   have hp : X ((B).adj θ d timeAxis x₁)= S.adj (H₁).spin d timeAxis (X x₁):=by
       unfold Table.adj; simp only [LinearMap.comp_apply];
       rw [← he.real, ← A.signed d]; rw[he.axis]; exact F.phase.transport.spots.signed _ _ _ -- need turnC/L.awareness
   change K! s (X x₀) (X x₁)=_; rw [glass_reads]; congr 2; funext i;fin_cases i; rfl;exact hp.symm
include P
lemma forms (s:Set (Points 2))(hs:IsCompact s)(hp:s⊆conf 2)(ε:ℝ)(he:0<ε): ∀ᶠ r in Pilot.trail,∀ x∈s, ‖arcPrice F d (Y r d) (r • x) - glass (Bel C.book) θ d x‖ ≤ ε:=by
   let W (z : ℝ×Points 2):= arcPrice F d (Y z.1 d) (z.1 • z.2)- U! z.2
   have ht : Tendsto W (Pilot.trail ×ˢ principal s) (𝓝 0):=by
      apply formsLimits _ _; intro x y
      let q: Ribbon (Bel C.book) (fun _ : Fin 2=> d):= ![x,(Bel C.book).adj θ d timeAxis y]
      apply Metric.tendsto_nhds.mpr; intro b hb
      filter_upwards [prod_mem_prod ((P.scheme F _ d).and (P.runs _ _ (fun _=>q) q (fun i=> tendsto_const_nhds) s hs hp (b/2) (half_pos hb)))
        (show s ∈ principal s from mem_principal.mpr subset_rfl)] with z ⟨⟨hz,hz'⟩,hw⟩
      change dist (W z x y) (0:ℝ)<_
      change dist ((arcPrice F d (Y z.1 d) _ x y) - U! z.2 x y) (0:ℝ)<_; rw [echo F d x y _ hz,glass_reads,dist_zero_right, ← Complex.sub_re]
      exact ((Complex.abs_re_le_norm _).trans (hz' _ hw)).trans_lt (half_lt_self hb)
   obtain ⟨O,hW,R,hR,he'⟩:= mem_prod_iff.mp ((stayNear ht he): ∀ᶠ p:ℝ×Points 2 in Pilot.trail ×ˢ principal s,‖W p-0‖≤ε)
   filter_upwards[hW] with i hi x hx; have h₁:= he' (show (i,x)∈ O×ˢ R from ⟨hi,(mem_principal.mp hR hx)⟩); change ‖W (i,x)-0‖≤ε at h₁; rw[sub_zero (W (i,x))] at h₁; exact h₁
lemma peaks : Tendsto (fun r=> arcPrice F d (Y r d) (r • D₂)) Pilot.trail (𝓝 (Weak.Portfolio.model C d)):=by
   refine (Metric.tendsto_nhds (a:= Weak.Portfolio.model C d) (u:=fun r=> arcPrice F d (Y r d) (r • D₂))).mpr fun ε he=>?_ ; filter_upwards[forms F P d (singleton detectors) isCompact_singleton (singleton_subset_iff.mpr detectors_in) (ε/2) (half_pos he)] with i hi; rw [dist_eq_norm (arcPrice F d (Y i d) _) (Weak.Portfolio.model C d)]; exact lt_of_le_of_lt (hi detectors rfl) (half_lt_self he)
local notation "W"=> (Weak.Portfolio.model C d)
local notation "δ"=>Lenses.margin C d/2
lemma heights : ∀ᶠ r in Pilot.trail, coercive (arcPrice F d (Y r d) (r • D₂)) δ ∧ ‖arcPrice F d (Y r d) (r • D₂)‖ ≤ δ+‖W‖:=by
   obtain ⟨hc,hU⟩:= (Weak.Portfolio.freely (C:=C) d).choose_spec
   filter_upwards[stayNear (peaks F P d) (half_pos hc)] with i hi; exact ⟨absorb _ _ _ _ hU (by simpa only [Lenses.margin,sub_half] using hi),normBy hi⟩
lemma all_motion (s:Set (Points 2))(hs:IsCompact s)(hp:s⊆conf 2):∃ K:ℝ,0 ≤ K ∧ ∀ᶠ r in Pilot.trail,∀ x∈s,‖arcPrice F d (Y r d) (r • x)‖ ≤ K:=by
   have he : ContinuousOn U! s:= fun x hx=> formsLimits _ _ fun a b=>by
      let q: Ribbon (Bel C.book) (fun _ : Fin 2=>d):=![a,(B).adj θ d timeAxis b]
      let f(y):=(B).classMoment (B) (fun _=> d) y q
      refine (Complex.continuous_re.continuousAt.tendsto.comp ( (show ContinuousOn f (conf _) from
        (smoothDisc (T:=Bel C.book) (H₀).smooth (hang _ q)).continuousOn).mono hp x hx)) -- type
   obtain ⟨w,hw⟩:= (hs.image_of_continuousOn (f:=fun x=> ‖U! x‖) ((continuous_norm (E:=RealForm ((B).Field d) ((B).Field d))).continuousOn.comp he (mapsTo_univ _ _))).bddAbove
   refine ⟨1 + max w 1,by positivity,?_⟩; filter_upwards[forms F P d s hs hp 1 zero_lt_one] with i hi x hx
   exact (normBy (hi x hx)).trans (add_le_add le_rfl ((show ‖U! x‖ ≤ w from hw (mem_image_of_mem _ hx)).trans (le_max_left ..)))

-- one interval neighborhood. TWO both directions via positive detector after tilt. No regularity of Y. coherence *between* stations costs ≤ polynomial ratio later.
omit P in
private lemma emits {k r:ℝ} (_hr:0<r) (h:coercive (arcPrice F d (Y r d) (r • D₂)) δ) (Z:Spin.change S d) (hk:‖arcPrice F d Z (r • D₂)‖≤ k) (v:S.Field d) : ‖(Y r d).symm v‖ ≤ Real.sqrt (k/(δ)) * ‖Z.symm v‖:=by
    apply bodyBound (half_pos ((Weak.Portfolio.freely (C:=C) d).choose_spec.1)) ((norm_nonneg (arcPrice F d Z _)).trans hk) (norm_nonneg _) (norm_nonneg _)
    set z:= r • D₂
    calc
       _ ≤ arcPrice F d (Y r d) z ((Y r d).symm v) ((Y r d).symm v):= h _
       _ = arcPrice F d Z z (Z.symm v) (Z.symm v) := by
            unfold arcPrice; simp_rw[pullBoth_read]; change K! z (Y r d _) (Y r d _) = K! z (Z _) (Z _); rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
       _ ≤ _ := (realUpper _ _).trans (mul_le_mul_of_nonneg_right hk (sq_nonneg _))
local instance: ContinuousSMul ℝ (Points 2):= IsBoundedSMul.continuousSMul
structure Both {A E : Type*}[NormedAddCommGroup A][NormedSpace ℂ A][AddCommGroup E][Module ℂ E](K:ℝ)(T U:A ≃ₗ[ℂ] E):Prop where
   left : ∀ x:E, ‖T.symm x‖ ≤ K*‖U.symm x‖
   right: ∀ x:E, ‖U.symm x‖ ≤ K*‖T.symm x‖
-- eventually cost but all sufficiently small (for chain). Orientation topology W.not infinitely ok. pricelist.
lemma throughout : ∃ K:ℝ,0<K∧ ∃ L:ℝ,0<L∧∀ r s:ℝ,0<r → r ≤ s → s ≤ L → s ≤ 2*r → Both K (Y r d) (Y s d):=by
   let f(x:ℝ):= x • D₂; let U:= Icc (1/2:ℝ) 2; have hv:0 < (1/2:ℝ):= half_pos zero_lt_one
   have he:Continuous f:= by fun_prop
   obtain ⟨K,hK,hp⟩:= all_motion F P d (f '' U) (isCompact_Icc.image he) (by rintro x ⟨x,hx,rfl⟩; exact Annulus.detector_in (hv.trans_le hx.1))
   let y:=Real.sqrt (K/(δ))
   obtain ⟨L,hL,hw⟩:= (nhdsGT_basis_Ioc (0:ℝ)).mem_iff.mp ((heights F P d).and hp)
   refine ⟨1+y, by unfold y; positivity,L,hL,fun r s hr ht hs hr'=> ?_⟩
   have hy:0<s:=hr.trans_le ht
   have hR:=hw (show r∈ Ioc (0:ℝ) L from ⟨hr,ht.trans hs⟩); have hS:=hw (show s∈ Ioc (0:ℝ) L from ⟨hy,hs⟩)
   have hp (s r:ℝ) (h:0 < s) : s • f (r/s) = r • D₂:= by unfold f; rw [smul_smul,mul_comm,div_mul_cancel₀ _ h.ne'] -- direction? mul_div_cancel₀
   constructor
   · intro x; refine (emits F d hr hR.1.1 _ ?_ x).trans (mul_le_mul_of_nonneg_right (show y ≤ 1+y from le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
     rw [← hp s r hy]; apply hS.2 (f (r/s)) (mem_image_of_mem _ ⟨(le_div_iff₀ hy).mpr (by linarith),(div_le_iff₀ hy).mpr (by linarith)⟩)
   intro x; refine (emits F d hy hS.1.1 _ ?_ x).trans (mul_le_mul_of_nonneg_right (show y ≤ 1+y from le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
   rw [← hp r s hr]; apply hR.2 (f (s/r)) (mem_image_of_mem _ ⟨(le_div_iff₀ hr).mpr (by linarith),(div_le_iff₀ hr).mpr hr'⟩)
end YM.Pier.Lair
