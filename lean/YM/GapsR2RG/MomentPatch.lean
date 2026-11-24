import YM.GapsR2RG.Jobs
import YM.OPE.Strobe.Nucleus
/-!
# Recenter any nonempty subproduct on the given bare sample for error propagation,
then assemble using all products containing a designated upper-history error.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsR2RG
open OPE OPE.Yarn OPE.Strobe
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol OPE.Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
section algebra
variable {J Ω:Type} [Fintype J][DecidableEq J][MeasurableSpace Ω] 
def scratchX (W:Bool→ J→Ω→ℂ)(S R:Finset J) := (fun x:Ω => ∏ j∈(S ∪ R:Finset J), (W (j∈S)) j x)
-- BOOL coercion
lemma soluble (μ:Measure Ω) (w:Bool→J→Ω→ℂ) (a b:J→Ω→ℂ) (c:J→ℂ)
    (ha:∀ j, a j-b j=w true j)(hb:∀ j x,a j x = w false j x + c j)
    {h v:ℝ}(hv:1≤v)(hc:∀ i,‖c i‖ ≤ v)
    (hi:Integrable (fun x=>∏ j:J,a j x) μ)
    (hx:∀ S R:Finset J,R⊆Sᶜ→ Integrable (scratchX w S R) μ)
    (hm:∀ S R:Finset J,R⊆Sᶜ → S.Nonempty → ‖∫ x,(scratchX w S R) x∂ μ‖ ≤ h):
    ‖(∫ x,∏ i:J,a i x ∂ μ) - (∫ x,∏ i:J,b i x ∂ μ)‖ ≤ 2^(2*Fintype.card J)*v^Fintype.card J * |h|:=by
    let θv (S R:Finset J):ℂ:= if S.Nonempty then - (-1)^S.card * ∏ i∈ Sᶜ \ R,c i else 0
    have eq(x:Ω): (∏ i:J,b i x)= (∏ i:J,a i x) + (∑ S:Finset J,∑ R∈ Sᶜ.powerset, -θv S R * (scratchX w S R) x):=by
       have ht : (∏ i:J,a i x)= ∑ S:Finset J, if S.Nonempty then 0 else (∏ i,a i x) * ∏ i∈S,w true i x:=by
           rw [Finset.sum_eq_single ∅]; simp
           · intro s _ hs; simp [Finset.nonempty_iff_ne_empty.mpr hs]
           · simp
       nth_rewrite 1 [ht]
       simp_rw [show ∀ i,b i x = a i x - w true i x from fun i=>by rw [← ha,Pi.sub_apply,sub_sub_cancel]]
       rw [←sum_add_distrib]; rw [Finset.prod_sub]
       simp only [Finset.powerset_univ]; apply Finset.sum_congr rfl; intro S _
       by_cases hs:S.Nonempty; swap; · have hs:= Finset.not_nonempty_iff_eq_empty.mp hs; subst S; simp [θv]
       rw [if_pos hs,zero_add,mul_assoc] -- edit
       simp_rw [hb]; rw [Finset.prod_add]; rw [sum_mul,mul_sum]
       refine sum_congr rfl (fun t ht=>?_); have ht':t ⊆ Sᶜ:= mem_powerset.mp ht
       have hz: Disjoint S t:= by simpa only [le_compl_iff_disjoint_right,disjoint_comm] using ht' -- unknown
       simp only [θv,if_pos hs,neg_mul,neg_neg]
       dsimp only [scratchX]; rw [prod_union hz]; have h₁: (∏ j∈ S,w (decide (j∈S)) j x)=(∏ j∈S,w true j x) :=prod_congr rfl fun j hj=>by simp [hj]
       have h₂: (∏ j∈ t,w (decide (j∈S)) j x)=(∏ j∈t,w false j x) :=prod_congr rfl fun j hj=>by simp [mem_compl.mp (ht' hj)]
       rw [h₁,h₂]; simp only [Finset.compl_eq_univ_sdiff]; ring
    let Y S R x:= -θv S R * scratchX w S R x; have hy (S R)(hR:R∈Sᶜ.powerset): Integrable (Y S R) μ:= (hx S R (mem_powerset.mp hR)).const_mul _
    have ha' S:= integrable_finsetSum (s:=Sᶜ.powerset) (hy S)
    simp_rw [eq]; rw [integral_add hi (integrable_finsetSum (s:=Finset.univ) (fun S _=>ha' S)), ← neg_sub,add_sub_cancel_left]
    change ‖- (∫ x,(∑ S:Finset J,∑ R∈Sᶜ.powerset,Y S R x)∂ μ)‖ ≤ _
    rw [ integral_finsetSum _ (fun S (_:S∈(univ:Finset (Finset J)))=>ha' S)]; simp_rw [integral_finsetSum _ (hy _)]; rw [norm_neg]
    let z:=Fintype.card J; let B:=v^z; have hb':0≤ B:= pow_nonneg (zero_le_one.trans hv) _
    have hθ S R (hR:R⊆Sᶜ): ‖∫ x,Y S R x∂ μ‖ ≤ B*|h|:=by
       unfold Y θv; split
       · rename_i hS; rw [integral_const_mul,norm_mul]; apply mul_le_mul ?_ ((hm S R hR hS).trans (le_abs_self _)) (norm_nonneg _) hb'
         unfold B; rw [norm_neg, norm_mul, norm_prod]; simp only [norm_neg,norm_pow,norm_one,one_pow,one_mul]; exact (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>hc i)).trans ((prod_const v).trans_le (pow_le_pow_right₀ hv (card_le_univ _)))
       simpa using! mul_nonneg hb' (abs_nonneg h)
    have hh S:= ((norm_sum_le _ _).trans (sum_le_sum (fun R hR=> hθ S R (mem_powerset.mp hR))): ‖∑ R∈ Sᶜ.powerset,∫ x,Y S R x∂ μ‖ ≤ _)
    refine ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun S _=>hh S))).trans ?_
    calc ∑ S:Finset J,∑ _∈ Sᶜ.powerset, B*|h| ≤ ∑ S:Finset J,∑ _:Finset J, B*|h|:= sum_le_sum (fun S _=>Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> mul_nonneg hb' (abs_nonneg h)))
         _ = _:=by simp [B,z,Fintype.card_finset,show 2*Fintype.card J=Fintype.card J + Fintype.card J by omega,pow_add]; ring
end algebra
open GridApprox
set_option quotPrecheck false
variable {I J:Type}[Fintype J][DecidableEq J]{E:ℕ}{G:Gauge}{C:Family G}{d:J→ℕ}
variable {W r D}{σ γ:ℕ→ℝ} (H:Yarn.Tune C W r D σ γ)
    {φ:Filter I}{k n:I→ℕ}(L : GracesP C φ k n)
variable (H₀:Citizen C W r D)(hE:0<E){v s:I→ℝ}
    (hv:Coins φ (C.S.scale ∘ k) v)(hv':∀ᶠ i in φ,1≤v i)
    (hs:Coins φ (C.S.scale ∘ k) s) (hs':∀ᶠ i in φ,0<s i)
def Rooms (C:Family G)(k p n E:ℕ)(x:J→Site (C.side k p)) := ∀ j l,j≠l→n≤ separation (x j) (x l) ∧ separation (x j) (x l) ≤ E*n
local notation "β" N p => C.beta N p -- parse issues
section fixed
variable {k' N p d' : ℕ} (x y : Site (C.side k' p))(a:ℕ)(L':C.label d')(h:k'≤N)(hx:C.ref d' ≤ k')(ice:Bool)
include H hx
lemma position : writeF C L' N k' p a (x+y) h ice = writeF C L' N k' p a x h ice ∘ pull 1 (anchor C.S p h y):=by
    let f:=betaDrop C d' k' N p a L' x ice; let F:=writeF C L' N k' p a x h ice
    have hξ : betaDrop C d' k' N p a L' (x+y) ice=f ∘ pull 1 y:= by
       unfold f betaDrop bead radiant; split; swap; · rfl
       funext U; simp only [Pi.neg_apply,stepUp, Function.comp_apply, Pi.smul_apply, smul_eq_mul, ↓reduceIte]; rw [pull_pull]; simp [affine,add_comm]
    have hA: y=anchor C.S p (le_refl k') y:= ((there y).symm.trans (vect C k' p k' y le_rfl)); have hp:= backTo_orient C.path N p (h:=k') le_rfl h y (1:Signed) (show Envelope f from cylinder_env (dropped H _ _ hx h a ice))
    rw [← hA] at hp; unfold writeF; rw [hξ,hp]; funext U
    have ht : anchor C.S p h (x+y)=anchor C.S p h x+anchor C.S p h y:= ((C.S.toDepth h p).root.map_add x y)
    change C.O N p L' _ U+_= C.O N p L' (anchor C.S p h x) (pull 1 (anchor C.S p h y) U)+_
    rw [ht]; congr 1; rw [pull_one,C.translation]
end fixed

section coupon
include H L H₀ hE hv hv' hs hs'
open Yarn.SitePlan Next.Rank.Station
lemma subset_coupon (T:Finset J)(i₀:↥T)(ice:↥T→Bool)(hh:ice i₀=true) :
    ∀ᶠ i in φ, ∀ (N p:ℕ) (h:k i<N)(x:J→Site (C.side (k i) p)), Rooms C (k i) p (n i) E x→
    ∀ q:(j:J)→C.label (d j), (∀ j, Spindle.paid C (d j) (k i) N p (q j) ≤ v i) →
      ‖Wilson.moment (C.beta N p) (fineJob (fun j:↥T => writeF C (q j) N (k i) p (C.path.levels.budget (k i)).B (x j.val) h.le (ice j)) univ)‖ ≤ s i :=by
    obtain ⟨z,hz,hM⟩:= ((eventually_gt_atTop (C.ref 0)).and (rolls H 0 (Fintype.card ↥T))).exists
    filter_upwards [bounded_jobs_wide (d:=fun i:↥T=> d i.val) H L hE ice i₀ hM hz H₀ i₀ hh hv (hv'.mono (fun i hi=> zero_lt_one.trans_le hi)) hs hs', L.seeks.eventually_ge_atTop z,eventually_all.mpr (fun j=> L.seeks.eventually_ge_atTop (C.ref (d j)))] with i hi _ hid N p h x hx q hq -- inspect d explicit
    let a:= (C.path.levels.budget (k i)).B; let x' (j:↥T):= x j-x i₀; have ht:Annular C (k i) p (n i) E x' i₀ := by
       refine ⟨sub_self _,fun j=>?_,fun j l h=>?_⟩
       · by_cases h:j=i₀; subst j; unfold x'; simp [separation_self]
         · exact (show pdist (x j - x i₀)≤_ from (hx j i₀ (mt Subtype.ext h)).2) |> le_trans (by change pdist _ ≤ _; rw [sub_zero])
       exact (show separation (x j) (x l)≥_ from (hx j l (mt Subtype.ext h)).1).trans_eq (congr_arg pdist (by unfold x'; abel)) -- unfold lhs if needed
    let f:= fineJob (fun j:↥T=> writeF C (q j) N (k i) p a (x' j) h.le (ice j)) univ; let V:= anchor C.S p h.le (x i₀)
    have hp:Integrable f (Wilson.law G (C.side N p) (C.beta N p)):= (Envelope.prodC univ _ (fun (j:↥T) _=>write_e H (q j.val) a (x' j) h.le (hid j) (ice j))).integrableC _
    have heq: (fineJob (fun j:↥T => writeF C (q j) N (k i) p a (x j.val) h.le (ice j)) univ)=f ∘ pull 1 V:=by
       funext U; exact Finset.prod_congr rfl fun j hJ=> by have eq:=congr_fun (position H (x' j) (x i₀) a (q j) h.le (hid _) (ice j)) U; rwa [show x' j + x i₀=x j from sub_add_cancel _ _] at eq
    rw [show (fineJob (fun j:↥T => writeF C (q j) N (k i) p (C.path.levels.budget (k i)).B (x j.val) h.le (ice j)) univ)=_ from heq, Wilson.moment_pull _ _ _ _ hp]; exact hi N p h x' ht (fun j=>(q j)) fun j=>hq j
end coupon
local notation "RF" => C.path.levels
local notation "gF" i => (C.path.levels.budget (k (i))).B
local notation "δslot" => (fun i:J=>C.label (d i))
def nominal (C:Family G) {d:J→ℕ}(N k p:ℕ)(x:J→Site (C.side k p))(q:(i:J)→ C.label (d i)):ℂ:=
    ∫ U,∏ i:J,bead C (d i) k N p (C.path.levels.budget k).B (q i) (x i) U∂ Therm.scene C.path N p k

def unmaskedT (C:Family G) {d:J→ℕ}(N k p:ℕ)(h:k≤N)(x:J→Site (C.side k p))(q:(i:J)→C.label (d i)):ℂ:=
    moment (C.beta N p) (fineJob (fun i:J=>abrade C (q i) N k p (x i) h) univ)
include H L H₀ hE hv hv' hs hs'
set_option maxHeartbeats 600000 in
theorem paid_many : ∀ᶠ i:I in φ,∀ N p (h:k i<N)(x:J→Site (C.side (k i) p)), Rooms C (k i) p (n i) E x→ ∀ q:(j:J)→C.label (d j), (∀ j, Spindle.paid C (d j) (k i) N p (q j) ≤ v i) →
    ‖unmaskedT C N (k i) p h.le x q - nominal C N (k i) p x q‖ ≤ s i :=by
    let z:= Fintype.card J; let B(i:I):ℝ:= 2^(2*z)*(v i)^z; let s'(i:I):=s i/B i; have hm:=C.S.divergent.comp L.seeks
    have hB: Coins φ (C.S.scale ∘ k) B:= Coins.mul (Bi.const _ (by dsimp [z]; positivity: (2:ℝ)^(2*z)≠0) hm) (Coins.power hv hm z)
    have hB₀:=hv'.mono fun i hi=> mul_pos (pow_pos (show 0<(2:ℝ) by norm_num) (2*z)) (by exact pow_pos (zero_lt_one.trans_le hi) z); have hx:= Coins.div hs hB; have hx':∀ᶠ i in φ, 0<s' i:= (hs'.and hB₀).mono fun i hh=> div_pos hh.1 hh.2
    obtain ⟨z',hz',hr⟩:= ((eventually_gt_atTop (C.ref 0)).and (rolls H 0 z)).exists
    have ht (S R:Finset J): ∀ᶠ i in φ, ∀ (N p:ℕ) (h:k i<N)(x:J→Site (C.side (k i) p)), Rooms C (k i) p (n i) E x→
      ∀ q:(j:J)→C.label (d j), (∀ j, Spindle.paid C (d j) (k i) N p (q j) ≤ v i) → R⊆Sᶜ → S.Nonempty →
      ‖Wilson.moment (C.beta N p) (scratchX (fun ice j=>writeF C (q j) N (k i) p (C.path.levels.budget (k i)).B (x j) h.le ice) S R)‖ ≤ s' i:=by
        by_cases he:S.Nonempty; swap; · exact Eventually.of_forall (by intros; contradiction)
        obtain ⟨j,hj⟩:=he; let T0 := S∪R; let j':↥T0:= ⟨j, Finset.mem_union_left R hj⟩; have hj':decide (j'.val∈S)=true:= by simp [j',hj]
        filter_upwards [subset_coupon H L H₀ hE hv hv' hx hx' T0 j' (fun j:↥T0=> j.val∈S) hj'] with i hc N p h x hx q hq _ _
        convert (hc N p h x hx q hq) using 1; congr 2; funext U
        exact Finset.prod_subtype _ (p:=fun i=>i∈T0) (by intro i; rfl) (f:=fun j=>writeF C (q j) N (k i) p (C.path.levels.budget (k i)).B (x j) h.le (j∈S) U) 
    filter_upwards [eventually_all.mpr fun S=>eventually_all.mpr (ht S),retreats (E:=E) H L H₀ d 0 z hr hz', hB₀, hx',hv'] with i hi hA hB0 hs0 hV N p h x hx0 q hq
    let m(j):= omen C (d j) (k i) (gF i); let A(j):=abrade C (q j) N (k i) p (x j) h.le; let Q(j):=bead C (d j) (k i) N p (gF i) (q j) (x j)
    let D(j):= backTo C.path N p h.le (Q j); let Q':=fineJob Q univ
    have hg:(∫ U,∏ j,D j U∂ Wilson.law G _ (C.beta N p))=nominal C N (k i) p x q:=by
        have ht(j):= bead_local H (x j) (q j) (hA.every j).rank h.le (gF i); have hT:Envelope Q' := Envelope.prodC _ _ (fun j _=> cylinder_env (ht j)); let M:=univ.sup m
        change moment (C.beta N p) (fineJob D univ) = _; unfold D
        rw [← backs_many C.path M N p (k i) N x _ (fun j=>(ht j).enlarges fun _ hy=>sparrow.mpr ((sparrow.mp hy).trans (Finset.le_sup (f:=m) (Finset.mem_univ j)))) ?_ h.le]
        · exact (Therm.onstage H.seed.wilson _ ((backTo_env _ _ _ _ hT).integrableC _)).symm.trans (Therm.retro H.seed.wilson h.le le_rfl Q' hT)
        intro j l he; obtain ⟨j',hj',heq⟩:=Finset.exists_mem_eq_sup _ (show (univ:Finset J).Nonempty from ⟨j,Finset.mem_univ _⟩) m
        unfold M; rw [heq]; exact ((hA.every j').gain.trans_le ((hA.every j).paid.trans ((hx0 j l he).1)))
    let c(j:J):= cameo C (d j) (k i) N p (q j); let W' (ice:Bool)(j:J):=writeF C (q j) N (k i) p (gF i) (x j) h.le ice
    have ha(j:J): A j - D j = W' true j:= (erased (C:=C) (q j) (gF i) (x j) h.le true).symm
    have hb(j:J):A j= W' false j + fun _=> c j:=by funext V; change A j V=(W' false j) V+c j; unfold W'; rw [erased]; simp [A,c]
    let νX:=Wilson.law G (C.side N p) (C.beta N p)
    -- expand all not just pair; every residual term has a designated true slot in a recentered subarray
    refine le_trans (hg ▸ soluble νX W' A D c ha (fun j=>congr_fun (hb j)) hV (fun j=>cameo_price (ρ:=v i) _ (hq j)) ?_ ?_ (fun S R hT hh=> hi S R N p h x hx0 q hq hT hh)) ?_
    · change B i * |s' i| ≤ s i; rw [abs_of_pos hs0]; unfold s'; field_simp [(show 0<B i from hB0).ne']; exact le_rfl
    · exact (Envelope.prodC _ _ fun j _=> Envelope.compactC (C.continuousO N p (d j) (q j) (anchor C.S p h.le (x j)))).integrableC _
    · intro S R _; exact (Envelope.prodC _ _ fun j _=> write_e H (q j) (gF i) (x j) h.le (hA.every j).rank _).integrableC _
end YM.GapsR2RG
