import YM.FullVolume.Strings
/-!
# Paired tails at full mesh & pulse period

An extra exercise toward authentic RoundMeter grid statements. Text invokes the assertions
from its B earlier on the unselected values of S in fullMesh. Prove using
original project `Extraction.Order` on f and `FullVolume.FixedBounds`, `PositionsUV`. Not
asking an axiom of continuity/extension through ties on these full meshes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells
open FullVolume
open Metric
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{n p :ℕ}
-- local notation requires hygiene; use explicit.
variable {F:ℕ→Positions n→ℂ}{w: Fin n→ C.book.Token}{L:Points n→ℂ} {K:Set (Points n)}
lemma cluster_uniform (H:Cluster C Extraction.Sequence.full p n F L)(hK:IsCompact K)(hS:K⊆NoHit C.S p n)(ε:ℝ)(h:0<ε):
    ∀ᶠ N in atTop,∀ x:Positions n,tag (C.S.a N) x∈K→ dist (F N x) (L (tag (C.S.a N) x)) ≤ ε:= by
    by_contra! hv
    obtain ⟨s,hs,X⟩:= extraction_of_frequently_atTop hv; choose y hy hF using X
    obtain ⟨x,hx,w,hw,hW⟩:= hK.tendsto_subseq hy; have hh:=(H.2 x (hS hx) (fun i=> y (w i)) (s ∘ w) (hs.tendsto_atTop.comp hw.tendsto_atTop) hW)
    let z(i):=tag (C.S.a (s (w i))) (y (w i)); have Hp:Tendsto (fun i=> L (z i)) atTop (𝓝 (L x)):= ((H.1.continuousAt ((nohitOpen _ _ _).mem_nhds (hS hx))).tendsto.comp hW)
    obtain ⟨i,hi⟩:= ((hh.dist Hp).eventually_le_const (show dist (L x) (L x)<ε from (dist_self _).trans_lt h)).exists; exact (hF _).not_ge hi
variable {S:Table C.book}
lemma compatible_mesh (H:Cluster C Extraction.Sequence.full p n (fun N=>lifted C N p w) L)
    (f:Extraction.Order){P:ℕ→Table C.book}(he:f.Meshes C P) (x:Points n)(hx:x∈Cyclic C.S p n): L x = (P p).read x w := by
    let N(i:ℕ):= f.mesh i; let y(i):= address (C.S.a (N i)) x
    have hp: x∈NoHit C.S p n:= fun i j he=> ⟨0,hx i j he 0⟩
    have hY:= (Extraction.chosen (S:=C.S) x).comp f.mesh.cofinal
    exact tendsto_nhds_unique (H.2 x hp y N f.mesh.cofinal hY) (f.evaluated C he p n w x hx y hY)
-- uniform local segment Lipschitz for actual `gKernel` in true units, not on Cyclic. variant Region. Uniform period too.
variable (H:FixedBounds C)
include H
private lemma margins (w:Fin n→C.book.Token)(l:List (MotionIndex n))(hK:IsCompact K)(hx:K⊆conf n):
    ∃ B:ℝ,0≤B ∧ ∀ᶠ p:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ x:Positions n, tag (C.S.a i) x∈K → ‖gKernel C w l i p x‖ ≤ B:= by
 obtain ⟨r,hr,hR⟩:= Gaps.someGrows C.S hK hx; obtain ⟨b,hb,H⟩:= H.bounds n w l r hr; exact ⟨b,hb,hR.mono (fun p hp=> H.mono fun i hi x hx=> hi p x (fun u w hu=> gridSeparation C.S _ rfl (hp _ hx) _ _ hu.symm))⟩

set_option maxHeartbeats 400000 in
lemma axes (w:Fin n→C.book.Token)(l:List (MotionIndex n))(hK:IsCompact K)(hx:K ⊆ conf n):
    ∃ r B:ℝ,0<r ∧ 0≤B ∧ ∀ᶠ p:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ x y:Positions n, tag (C.S.a i) x∈K →
    dist (tag (C.S.a i) y) (tag (C.S.a i) x)≤r → dist (gKernel C w l i p y) (gKernel C w l i p x) ≤ B * dist (tag (C.S.a i) y) (tag (C.S.a i) x):= by
    obtain ⟨r,hr,hT⟩:= hK.exists_cthickening_subset_open (conf_open _) hx
    choose B hb h using fun i:MotionIndex n=> margins H w (i::l) hK.cthickening hT
    let b:= ∑ i:MotionIndex n,B i; have hc:0≤b:= Finset.sum_nonneg fun i _=>hb i
    refine ⟨r,b*Fintype.card (MotionIndex n),hr,mul_nonneg hc (Nat.cast_nonneg _),?_⟩
    filter_upwards [eventually_all.mpr h] with p Hp; filter_upwards [eventually_all.mpr Hp] with i hi x y hx hy
    let t:=C.S.a i; let P:= gKernel C w l i p; refine stroll (C.S.a_pos _) P _ _ _ _ hc hy (fun u j hu=>?_)
    rw [dist_eq_norm,unique_units P (C.S.a_pos _) j u,norm_smul, Real.norm_of_nonneg (C.S.a_pos _).le]
    exact mul_le_mul_of_nonneg_left ((hi j u (mem_cthickening_of_dist_le _ _ _ _ hx hu)).trans (Finset.single_le_sum (fun i _=>hb i) (mem_univ _))) (C.S.a_pos _).le
lemma lips {L:ℕ→Points n→ℂ}(hp:∀ p:ℕ,Cluster C Extraction.Sequence.full p n (fun N=>lifted C N p w) (L p))(hK:IsCompact K)(hx:K⊆conf n):
    ∃ δ B:ℝ,0<δ ∧ 0≤ B ∧ ∀ᶠ p in atTop, ∀ x∈K, ∀ y∈K, dist y x<δ→ dist (L p y) (L p x)≤ B*dist y x:=by
 obtain ⟨t,ht,hK',hk⟩:= exists_compact_between hK (conf_open n) hx
 obtain ⟨r,b,hr,hb,H⟩:= axes H w [] ht hk
 refine ⟨r,b,hr,hb,?_⟩; filter_upwards [H,Extraction.room C.S ht] with p hp' h x hX y hy he
 let a (x:Points n)(i:ℕ):= address (C.S.a i) x; have hv (x:Points n):Tendsto (fun i:ℕ=> tag (C.S.a i) (a x i)) atTop (𝓝 x):= Extraction.chosen x
 have hV(x:Points n)(he:x∈K):Tendsto (fun i => lifted C i p w (a x i)) atTop (𝓝 (L p x)):=
    (hp p).2 x ((no_wrap_hit C.S (h (interior_subset (hK' he)))).2 (hx he)) (a x) id tendsto_id (hv x)
 refine le_of_tendsto_of_tendsto ((hV y hy).dist (hV x hX)) (((hv y).dist (hv x)).const_mul b) ?_
 filter_upwards [hp', ((hv y).dist (hv x)).eventually_le_const he, (hv x).eventually (mem_interior_iff_mem_nhds.mp (hK' hX))]
    with i hi hp ht; exact hi _ _ ht hp
end YM.Integration.GradedFar.Auth
