import YM.GapsContact.TubeCheckpoint
import YM.GapsContact.Jost.Route
/-!
# Jost costs use the same Gram budget

Pick up Stamps in an O(4)-aligned frame via the same path as Receipt. Here the horizon is
any one d throughout; no assertion (yet) of compatibility with nested horizons. Along *any length
sequence* on the same F pick good O(4) data (analytic label matrices are fixed through it).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Jost
open Function Filter Set Mink Mink.Poincare Boundary Boundary.Surface Bid Trace Trace.Pilot Trace.Terrace Trace.Over
open Analysis MeasureTheory Spec Spin Extraction Next.BOUNDARY
open scoped Topology BigOperators InnerProductSpace Classical NNReal
universe u
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
variable (F:Final C f S){hG:G.Simple}{n d:ℕ}
local notation "Y"=> Final.sector F
local notation "K"=> Wightman.spin (Final.action F)

private lemma one (u:S.Field d) : (K).shell d 1 u=u:=S.pin_inj _ ((F.realization.qt.letters.ties 1 d u).symm.trans (F.realization.qt.letters.identity _))
private theorem mult (a b : Lorentz) (v : S.Field d) :
    (K).shell d (a*b) v=(K).shell d a ((K).shell d b v) := by
  apply S.pin_inj; simpa only [F.realization.qt.letters.ties] using F.realization.qt.letters.representation a b (S.pin d v)

def Comm (A: S.Field d →L[ℂ] S.Field d) := ∀ t x, A ((Y).turns.act d t x) = (Y).turns.act d t (A x)

lemma Comm.motion {A:S.Field d→L[ℂ] S.Field d} (h:Comm F A) (b:Lorentz) (x:S.Field d): A ((K).shell d b x)=(K).shell d b (A x):=by
  let A':= A.restrictScalars ℝ
  let J:= K
  have ha (a:Ortho.Skew) (v:S.Field d): A ((Y).turns.lie d a v)=(Y).turns.lie d a (A v):=by
    have he := A'.hasFDerivAt.comp_hasDerivAt (0:ℝ) (F.phase.transport.spots.infinitesimal d a v)
    have hv(p:ℝ): A' ((Y).turns.act d (Ortho.oneParameter a p) v)=(Y).turns.act d (Ortho.oneParameter a p) (A' v):=h ..
    change HasDerivAt (A'∘ _) _ _ at he; simp_rw [Function.comp_def,hv] at he
    exact he.unique (F.phase.transport.spots.infinitesimal d a (A' v))
  have he(i:SpaceAxis)(x:S.Field d)(r:ℝ):A (J.shell d ((Ray.fromAxis i).boost r) x)=J.shell d ((Ray.fromAxis i).boost r) (A x):=by
    let D:=LinearMap.toContinuousLinearMap ((-Complex.I) • (Y).turns.lie d (Ortho.plane timeAxis i.castSucc)); let t(y:S.Field d):=fun s=>J.shell d ((Ray.fromAxis i).boost s) y
    have hv(y:S.Field d)(s:ℝ): HasDerivAt (t y) (D (t y s)) s:=by
       simpa only [t,Function.comp_def, one_smul,J,← mult,← Ray.boost_add,sub_add_cancel] using!
         (F.realization.qt.letters.boosts d i (t y s)).scomp_of_eq s ((hasDerivAt_id' s).sub_const s) (by simp)
    have ht(s):HasDerivAt (A' ∘ t x) (D (A' (t x s))) s:=by
       apply (A'.hasFDerivAt.comp_hasDerivAt s (hv x s)).congr_deriv; symm
       change -Complex.I • _ = A (-Complex.I • ((Y).turns.lie d _ (t x s))); rw [map_smul,ha]; rfl --?
    have hp: (A' ∘ t x) 0 = (t (A x)) 0:=by simp [t,J, one, A']
    apply congr_fun (ODE_solution_unique_univ (s:=fun _=>univ) (fun _=>D.lipschitz.lipschitzOnWith) (fun s=> ⟨ht s,Set.mem_univ _⟩) (fun s=> ⟨hv (A x) s,Set.mem_univ _⟩) hp) r
  have hp : b∈ Bid.beamGens := by rw [(Work.A16.answer: Bid.beamGens=⊤)]; trivial
  refine (Subgroup.closure_induction (p:=fun b _=> ∀ x:S.Field d,A (J.shell d b x)=J.shell d b (A x)) ?_ ?_ ?_ ?_ hp) x
  · intro b hb v
    rcases hb with ⟨s,t,rfl⟩|⟨a,u,rfl⟩
    · simp only [J,F.realization.qt.letters.spatial]; exact h s v
    exact he a v u
  · intro v; rw [show J.shell d 1 v=v from one F v, show J.shell d 1 _=_ from one F (A v)]
  · intro a b _ _ hp hu v; simp only [J,mult]; erw [hp,hu]
  intro a _ h v; apply (J.shell d a).injective
  rw [← h ((K).shell d a⁻¹ v),← mult F,← mult F]; simp [one]

open Complex in
lemma oftReal {P:ℂ→Prop}(h:∀ x:ℝ,P (x:ℂ)) : ∃ᶠ z in 𝓝[≠] (0:ℂ), P z :=by
    have hu : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]; refine ⟨?_, ?_⟩
      · simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0)))
      filter_upwards [self_mem_nhdsWithin] with r hr
      change (r : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (mem_Ioi.mp hr).ne'
    intro hx; obtain ⟨r, hr⟩ := (hu.eventually hx).exists; exact hr (h r)

-- Use same representation at every d (real boost holomorphic extension UNIQUE).
structure Blade (F:Final C f S)(d:ℕ)(r:Mink.Ray) where
   U : ℂ → (S.Field d→L[ℂ] S.Field d)
   hol : AnalyticOnNhd ℂ U univ
   line (t:ℝ) (v): U (↑t) v= F.action.spin.shell d (r.boost t) v
variable {F} {r:Mink.Ray}
lemma blade (F: Final C f S)(d:ℕ)(r:Mink.Ray) : Nonempty (Blade F d r):= by
    obtain ⟨U,h,p⟩:= Integrated.reconstructionArcs.cR _ _ _ F.realization.qt.letters d r; exact ⟨U,h,p⟩

def fly (F:Final C f S)(d:ℕ)(P:Scheme n) (A: Blade F d P.e) : S.Field d →L[ℂ] S.Field d:=
    (A.U (↑P.speed * Complex.I)).comp (LinearMap.toContinuousLinearMap (F.action.spin.shell d P.g).toLinearMap) --?
lemma Blade.attune (A:Blade F d r) (x:S.Field d):AnalyticOnNhd ℂ (fun z=> A.U z x) univ:= fun z hz=> by
    let L: (S.Field d →L[ℂ] S.Field d) →L[ℂ] S.Field d:= ContinuousLinearMap.apply ℂ (S.Field d) x
    exact (L.analyticAt _).comp (A.hol z hz)
lemma Blade.shift {A:S.Field d→L[ℂ] S.Field d}(h:Comm F A) (B:Blade F d r)(z:ℂ)(x:S.Field d):A (B.U z x)=B.U z (A x):=by
    let f(z:ℂ):= A (B.U z x);let g(z:ℂ):= B.U z (A x)
    have he : AnalyticOnNhd ℂ f univ:= fun z hz=> (A.analyticAt _).comp (B.attune _ z hz)
    have hh := B.attune (A x)
    apply he.eqOn_of_preconnected_of_frequently_eq hh isPreconnected_univ (Set.mem_univ (0:ℂ)) ?_ (Set.mem_univ z)
    exact oftReal fun t=> by change A (B.U (↑t) x)= B.U (↑t) (A x); rw [B.line,B.line]; exact Comm.motion _ h _ x

open Ascent Climb Next.UVStress MergeProof.East
variable (F) (hG)
variable {H:(Climb.Bel C.book).Hierarchy}{𝓛:Ultrafilter (ℕ×ℕ)} {Z:Arch C} {J:Scaling S}{V:∀ i,Vane C i}
variable {R W:change S d}
-- for transition relative to any two EXACT alignments with the reference representation
lemma coworkers (hr:AlignO F.sector F.room.kernel.spin H d R)(hw:AlignO F.sector F.room.kernel.spin H d W): Comm F (LinearMap.toContinuousLinearMap (R.symm.trans W).toLinearMap):=by
   intro i x; obtain ⟨z,rfl⟩:= R.surjective x; change W (R.symm _) = _; rw [← hr.axis]; change W (R.symm _)= F.sector.turns.act d i (W (R.symm _)); simp only [LinearEquiv.symm_apply_apply, hw.axis]

-- rotations and complex boosts, X calibration and all size budgets via this predicate
def Pathway (F:Final C f S)(H:(Bel C.book).Hierarchy)(d:ℕ)(B:S.Field d→L[ℂ] S.Field d) := ∀ R W:change S d, AlignO F.sector F.room.kernel.spin H d R→ AlignO F.sector F.room.kernel.spin H d W→ ∀ x:S.Field d, B (W (R.symm x))= W (R.symm (B x))

lemma rotation_path (P: Scheme n) (B:Blade F d P.e) : Pathway F H d (fly F d P B):=by
   intro R W hR hW x
   let Q:= LinearMap.toContinuousLinearMap (R.symm.trans W).toLinearMap; have hp : Comm F Q:= coworkers F hR hW
   change B.U _ ((K).shell _ _ (Q x))= Q (B.U _ ((K).shell _ _ x)); rw [B.shift hp, Comm.motion F hp P.g x]

section calibrated
-- comparing and constructing prospective receipt for other horizons
structure Stable (H:(Climb.Bel C.book).Hierarchy)(R:change S d)(B:ℝ)(s:ℝ):Prop where
   align : AlignO F.sector F.room.kernel.spin H d R
   budget : ∀ x:(Bel C.book).Field d, cost F d s (R x) ≤ B*‖x‖
   inverse : ∀ x:(Bel C.book).Field d, ‖x‖≤ B*cost F d s (R x)
lemma Stable.mono {s a b:ℝ}(h:Stable F H R a s)(ha:a≤b): Stable F H R b s:= ⟨h.align,fun x=> (h.budget x).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _)), fun x=> (h.inverse x).trans (mul_le_mul_of_nonneg_right ha (Ascent.cost_pos ..))⟩

include hG
lemma steady_scribe (hp:Scribe f J V Z F.sector 𝓛 F.room.kernel H)(d:ℕ):∃ U:ℕ → change S d, Tendsto (fun k=>moveV (S:=S) d (J.U k d) (U k)) atTop (𝓝 1) ∧ ∃ B:ℝ,1≤ B ∧ ∀ᶠ k in atTop,Stable F H (U k) B (J.r k):=by
   obtain ⟨U,hU,ha⟩:= alignsO hG hp d; obtain ⟨B,hB,h⟩:= window_prices F hG hp.monorail d 1 1 one_pos
   let T (k:ℕ):= moveV (S:=S) d (J.U k d) (U k)
   refine ⟨U,hU,B*2, le_trans hB (by linarith),?_⟩
   filter_upwards [ha,h,hU.eventually (Metric.ball_mem_nhds 1 (half_pos (show (0:ℝ)<1 from zero_lt_one)))] with k hk hK hT
   have hh : ‖T k-1‖ ≤ 1/2:=by rw [dist_eq_norm] at hT; exact hT.le
   have hx(x): ‖(T k) x - x‖ ≤ 1/2*‖x‖:= ((T k-1).le_opNorm x).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg x))
   have hv(x) : U k x=J.U k d (T k x):=(LinearEquiv.apply_symm_apply ..).symm
   refine ⟨hk,fun x=> ?_,fun x=>?_⟩
   · have hf:(T k) x=((T k) x-x)+x:=(sub_add_cancel ..).symm
     have ht : cost F d (J.r k) (U k x) ≤ B *‖T k x‖:=by rw [hv]; simpa only [mul_one] using (hK (T k x)).2 1 ⟨le_rfl,le_rfl⟩
     apply ht.trans; rw [mul_assoc B]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hB)
     exact (le_of_eq (congr_arg norm hf)).trans ((norm_add_le ..).trans (by linarith [hx x,norm_nonneg x]))
   have ht : ‖(T k) x‖ ≤ B * cost F d (J.r k) (U k x):=by rw [hv]; exact (hK _).1
   have h':‖x‖-‖(T k) x‖ ≤ 1/2*‖x‖:= by have h'':= norm_sub_norm_le x ((T k) x); rw[norm_sub_rev] at h''; exact h''.trans (hx x)
   linarith

lemma have_stable (X:Bliss F 𝓛 Z H)(d:ℕ): ∃ B:ℝ,1≤ B ∧ ∀ᶠ r in trail,∃ R:change S d,Stable F H R B r:=by
   by_contra! hx
   have ht(i:ℕ):∃ s:ℝ,0<s ∧ s<costHint i ∧ ∀ R:change S d, ¬ Stable F H R (sizeHint i) s:=by
      obtain ⟨s,h,h1,h2⟩:= ((hx (sizeHint i) (by unfold sizeHint; simp)).and_eventually ((show ∀ᶠ s in trail,0<s from self_mem_nhdsWithin).and ((gt_mem_nhds (Next.UVStress.cost_pos i)).filter_mono nhdsWithin_le_nhds))).exists; exact ⟨s,h1,h2,h⟩
   choose s h h' he using ht
   obtain ⟨m,hm,J,hJ,V,hV⟩:= X.picks s (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cost_clears (fun i=> (h i).le) (fun i=>(h' i).le)) h
   obtain ⟨U,-,B,-,hK⟩:= steady_scribe F hG hV d
   obtain ⟨i,hi,hp⟩:= (hK.and ((size_ascends.comp hm.tendsto_atTop).eventually_ge_atTop B)).exists
   rw [hJ] at hi; exact he (m i) (U i) (Stable.mono F hi hp)
lemma Pathway.payment (X: Bliss F 𝓛 Z H){B:S.Field d→L[ℂ] S.Field d}(hp:Pathway F H d B): ∃ A:ℝ,1≤ A ∧ ∀ᶠ r in trail,∀ v:S.Field d, cost F d r (B v)≤A* cost F d r v:=by
   obtain ⟨a,ha,ht⟩:= have_stable F hG X d; obtain ⟨r,R,hR⟩:=ht.exists -- omit r?
   let q:=LinearMap.toContinuousLinearMap ((R.symm.toLinearMap.comp B.toLinearMap).comp R.toLinearMap); let c:=max 1 ‖q‖
   have hb:1≤c:= le_max_left ..
   refine ⟨(a*c)*a,one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) ha,?_⟩
   filter_upwards [ht] with r ⟨W,hW⟩ v
   obtain ⟨y,rfl⟩:= W.surjective v
   rw [show B (W y)=W (q y) from ?_]; swap
   · change B (W y) = W (R.symm (B (R y))); simpa only [LinearEquiv.symm_apply_apply] using hp R W hR.align hW.align (R y) -- q unfolding?
   have hg: ‖q y‖≤c* (a*cost F d r (W y)):= (q.le_opNorm y).trans (mul_le_mul (le_max_right ..) (hW.inverse y) (norm_nonneg _) (zero_le_one.trans hb))
   exact (hW.budget _).trans ((mul_le_mul_of_nonneg_left hg (zero_le_one.trans ha)).trans_eq (by ring))
end calibrated
variable {F} {L:EveryPhase.Almanac F} {hG}
lemma fly_measured (hx:Roll.{u} F hG L) (P: Scheme n) (B:Blade F d P.e){v:ℝ→S.Field d} (h:Measured F d v):Measured F d (fun r=> fly F d P B (v r)):=by
   obtain ⟨H,W,ℓ,hU,-,-⟩:=hx.trace.stress
   obtain ⟨A,hA,hB⟩:= Pathway.payment F hG hU (rotation_path F P B)
   obtain ⟨c,hc,ht⟩:=h; exact ⟨A*c,mul_pos (zero_lt_one.trans_le hA) hc,(ht.and hB).mono fun r hr=> (hr.2 _).trans (mul_le_mul_of_nonneg_left hr.1 (zero_le_one.trans hA))⟩
end YM.GapsContact.Jost
