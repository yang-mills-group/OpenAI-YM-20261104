import YM.OPE.Compatible.Chain.Volt
import YM.OPE.Compatible.Bowman.Teller
/-!
# Ridge canopy covariance. Nonharmonic curl spends independent alps (yes origins also).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical
variable {G:Gauge}{n:Side}
open RG Bid Pressure Stationary Precision FreeResolvent WithLp Next.Free Frequency Streamer
variable (H:Even n.val)
def cloak: Keys G (Limb H)→L[ℝ] Bid.Dir G n:= LinearMap.toContinuousLinearMap {
    toFun p x:= hover H p (x.1,axisEquiv.symm x.2)
    map_add' a b:= by funext i; simp only [hover,Pi.add_apply];split_ifs with h; exact neg_add ..; rfl
    map_smul' a b:=by funext i;simp only [hover,Pi.smul_apply];split_ifs with h; exact (smul_neg ..).symm; rfl}
lemma cloak_at (u:Keys G (Limb H))(x:Site n)(i:Axis): cloak H u (x,coord i)=hover H u (x,i):=by
     change hover H u (x,axisEquiv.symm (axisEquiv i))=_; rw [Equiv.symm_apply_apply]
lemma cloak_e (u:Keys G (Limb H)): represent (cloak H u)=coat H (put u):=by
     rw [← hover_conduit]; funext i; rcases i with ⟨x,k⟩; rw [Work.F03.represent_link,cloak_at];rfl
lemma EllK (i:G.ColorIndex)(u:Keys G (Limb H)): Ell (loadV (parts G _ (cloak H u) i)):=by
      intro j e; have he(x:edgeV n):loadV (parts G _ (cloak H u) i) x=(hover H u x) i:=by rcases x with ⟨x,k⟩; unfold loadV parts; dsimp only;rw [cloak_at]
      rw [he,he,hoverEll H u j e]; split <;>rfl
lemma cuff (T:Plot H)(x: Keys G T.Free) (h:∀ i:G.ColorIndex,d 1 n*ᵥ (parts G _ (cloak H (T.rollX x)) i)=0):x=0:=by
    funext p; let u:=T.rollX x; ext i; obtain ⟨s,hs⟩:= h_grad H _ (EllK H i u) (h i)
    have ht(p:Limb H): (u p) i= s (cap H p)-s (foot H p):=by specialize hs p.val; dsimp only [loadV, Exterior.parts] at hs; rw [cloak_at,Prod.mk.eta,hover_reap] at hs; exact hs
    have he(o:Node H): s o=s (origin H):=by
        induction q:T.flick o using Nat.strong_induction_on generalizing o with
        | _ q ih=>
          by_cases hD:o=origin H
          · rw [hD]
          let v: ↥(({origin H}:Set (Node H))ᶜ):=⟨o,hD⟩; have ha := T.bump v; let k:=T.point v; have hk:(u k.1)=0:=T.keptZ _ _ (⟨_,T.purity v⟩ : T.Stable)
          have hy:s ((Pond H).start k)=s ((Pond H).lastV k):=by
               have hz:s (cap H k.1)=s (foot H k.1):=sub_eq_zero.mp ((ht k.1).symm.trans (congr_arg (fun p:G.Color=>p i) hk))
               unfold start lastV; split; exact hz; exact hz.symm
          rw [show o=(Pond H).start k from (T.root v).symm,hy]; exact ih _ (ha.trans_eq q) _ rfl
    change x p i=0; rw [show x p=u p.val from (T.kept 0 x p).symm, ht,he (cap H p.val),he (foot H p.val),sub_self]
variable {i:ℕ}{l:ℝ}{B:Sponsor G}{Q:Seasons B}
-- spectral metric
lemma rankcost (T:Plot H)(x:Keys G T.Free)(v:=flatten (cloak H (T.rollX x))) (A:Alps B Q i l)(h:4≤ i)(hx:x≠0)(p:v=flatten (cloak H (T.rollX x)):=by rfl): 0 < dotProduct v (tensor G (A.root.acts n)*ᵥ v):=by
    subst v; let k:=B.K; let γ:=k.penalty; let m:= pink γ A.gear; obtain ⟨c,M,hc,hm,D⟩ := (heart_heats γ k.penalty_pos h (fun i:Train i=> i)).1.funds; let P:= (heart_heats γ k.penalty_pos h (fun i:Train i=> i)).1
    let u:= cloak H (T.rollX x); let K:= A.root.acts n; have hp : K=Precision.K (m.acts n):= Op_stays h _ _; let W:= d 1 n
    rw [component_dot]; simp_rw [component_mul];
    have hg:= (obey_band _ (P.stock.whole A.gear) (D A.gear) n).2
    let F(p:G.ColorIndex):= parts G 1 u p
    let g(p:G.ColorIndex):= (F p) ⬝ᵥ (K *ᵥ F p)
    have he(p): c*((W *ᵥ F p) ⬝ᵥ (W*ᵥ F p)) ≤ g p:=by
        unfold g; rw [hp]; have hz:= (hg (W *ᵥ F p)).1; unfold Precision.K; -- use transpose
        change _ ≤ (F p) ⬝ᵥ ((((W.transpose)*(m.acts n)*W))*ᵥ F p)
        rw [← mulVec_mulVec,← mulVec_mulVec,dotProduct_mulVec (F p) Wᵀ, vecMul_transpose]; exact hz
    obtain ⟨p,hD⟩: ∃ p:G.ColorIndex,(W *ᵥ F p)≠0:=by by_contra! hv; exact hx (cuff H T x hv)
    change 0<∑ p:G.ColorIndex,g p; apply lt_of_lt_of_le _ (Finset.single_le_sum (s:=Finset.univ) (f:=g) (fun j _=> (mul_nonneg hc.le (show 0≤ dotProduct (W*ᵥ F j) _ from by simpa only [star_trivial] using dotProduct_star_self_nonneg (W*ᵥ F j))).trans (he j)) (Finset.mem_univ p)); exact (mul_pos hc (show 0< dotProduct (W*ᵥ F p) _ from by simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hD)).trans_le (he p)
end YM.OPE.Cascade
