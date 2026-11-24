import YM.TraceExtension.Atlas.Zone
import YM.PhysMS.Frame.Tensor
import YM.PhysMS.Frame.Repair

/-! # Near-identity multi-horizon frame supplied along every admissible
Scribe for the trace scheme. Also prove *angle condition* for its own F4 columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress MeterTest
open MergeProof.East Next.Rank Next.Rank.East Maxwell
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge}{C : Family G}{f : Extraction.Order}{S : Table C.book}
variable {Y : Ultrafilter (ℕ × ℕ)} (h : G.Simple) (F:Final C f S) (H:(Bel C.book).Hierarchy)
  {V:∀ i,Vane C i}{Z:Terrace.Arch C} (X:Scaling S) (hX:Over.Scribe f X V Z F.sector Y F.room.kernel H)
local notation "K" => Maxwell.Free.scheme C.labels
set_option quotPrecheck false
local notation "D" d => (Bel C.book).Field d

-- Determine inclusion at the leading scale. Can't just lift Near of an earlier unrelated X.
private lemma sees_inclusions {L:Register G}{S:Table L} (T:S.Smooth)(R:MeterTest S)
    (P:DiffPlan S) (hp:P.Inclusions S) (r:ℝ)(hr:0<r)(d:ℕ)(v:S.Field d) :
    R.checkAt T (d+1) r hr (P.rise (Nat.le_succ d) v) = R.checkAt T d r hr v := by
  apply R.t.apply_eq; intro x hx; exact hp.kernels _ _ (Work.A05.smul_conf hr hx) _
include hX
lemma observes : Adjacent F X.U atTop := by
  intro d v
  let p i := (X.U i (d+1)).symm (F.sector.derivatives.rise (Nat.le_succ d) (X.U i d v)); let w := (K).rise (Nat.le_succ d) v
  obtain ⟨s,hs⟩:= detects (Bel C.book) H (d+1)
  let A(k:ℕ):= LinearMap.pi (fun j:s=> rescaled F.room.kernel.smooth (isoPanel X k) j.val (X.r k) (X.positive k) (d+1))
  let W:= LinearMap.pi (fun j:s=>zeroScale j.val H.smooth (d+1)); refine Work.A04.tendsto_of_fitted A W (w:=p) hs ?_ (tendsto_pi_nhds.mpr fun j=>?_)
  · intro u; exact tendsto_pi_nhds.mpr (fun t=> reads_limit F.room.kernel.smooth H.smooth hX.monorail.approach (t:s).val (d+1) u)
  have ht:= reads_limit F.room.kernel.smooth H.smooth hX.monorail.approach (j:s).val d v
  change Tendsto _ _ (𝓝 ((j:s).val.checkAt H.smooth (d+1) 1 one_pos w))
  rw [show j.val.checkAt H.smooth _ 1 one_pos w = _ from sees_inclusions H.smooth j.val K (Free.scheme_filters C.labels) 1 one_pos d v]
  apply ht.congr; intro i; change _= rescaled F.room.kernel.smooth (isoPanel X i) (j:s).val (X.r i) (X.positive i) _ (p i); rw [rescaled,rescaled]; simp only [LinearMap.comp_apply, isoPanel,LinearEquiv.coe_coe,p,LinearEquiv.apply_symm_apply]; exact (sees_inclusions _ _ _ F.phase.transport.injection _ _ _ (X.U i d v)|>.symm)

omit hX X
section
variable {I:Type*} {l:Filter I} {A X P:I→tower S}
def localCost (l:Filter I)(X A:I→tower S):Prop:= ∀ (d:ℕ) (v:D d), Tendsto (fun i=> (X i d).symm (A i d v)) l (𝓝 v)
lemma localCost_trans (h : localCost l X P)(hp:localCost l P A):localCost l X A:=by
   intro d v
   have hv:= Dash.arcing (Dash.fit_plane (fun i=> (actMove d (X i d) (P i d) (S:=S)).toLinearMap) LinearMap.id (h d)) (hp d v)
   apply hv.congr; intro i; change (X i d).symm (P i d ((P i d).symm _))= _; rw [LinearEquiv.apply_symm_apply]
end
include X hX
lemma path_lead {A:ℕ→tower S} (hA:localCost atTop X.U A) (n:ℕ) (d:Caps n) (v:MaxwellSlots C d) (j:ℕ) (E:Set (Points n)) (he:IsCompact E) (ht:E⊆conf n) :
    TendstoUniformlyOn (fun i=> iteratedFDeriv ℝ j (measured F none (A i) v (X.r i))) (iteratedFDeriv ℝ j (WickGoal v)) atTop E:=by
  rw [Metric.tendstoUniformlyOn_iff]; intro ε hε; let w (k:ℕ) (i:Fin n):D (d i) := (X.U k _).symm (A k _ (v i))
  have hk (i:ℕ) : measured F none (A i) v (X.r i)= Next.UVStress.tested (X.r i) (isoPanel X i) (hang d (w i)) := by
     funext x; apply DFunLike.congr_arg (S.classMoment S d (X.r i • x)); exact funext fun k=> ((X.U i (d k)).apply_symm_apply _).symm
  filter_upwards [travels_jet F.room.kernel F.phase.transport.derivatives H
    (Maxwell.Free.scheme_derives C.labels) X hX.monorail.approach w v (fun i=> hA _ (v i)) j E he ht (ε/2) (half_pos hε)] with i hi x hx
  rw [dist_comm,dist_eq_norm,hk]; exact lt_of_le_of_lt (hi x hx) (half_lt_self hε)

include h X hX
lemma survey : ∃ A:ℕ→tower S, localCost atTop X.U A ∧ (∀ᶠ i in atTop, AtAngle (𝓛:=Y) (H:=H) F h (X.r i) (A i 4)) ∧
    (∀ d,∀ᶠ i in atTop, obedient F H (A i) d) ∧ ∀ d e (he:d≤e), ∀ᶠ i in atTop, ∀ v,
      A i e ((K).rise he v)= F.sector.derivatives.rise he (A i d v) := by
  obtain ⟨P,hP,hE⟩ := fulfill F h hX
  have hP₁ := latium F h hX P hP hE; choose A hA hA' using fun d=> alignsO h hX d
  let A' (i:ℕ) := update (β:=fun d=> change S d) (fun d=>A d i) 4 (P i)
  have ha : localCost atTop X.U A' := by
     intro d v; by_cases hd:d=4
     · subst d; simp_rw [A',update_self]; exact Dash.arcing hP (tendsto_const_nhds (x:=v))
     simp_rw [A',update_of_ne hd]; exact Dash.arcing (hA d) (tendsto_const_nhds (x:=v))
  have hu(d:ℕ) : ∀ᶠ i in atTop, obedient F H (A' i) d := by
     unfold obedient A'; by_cases he:d=4
     · subst d; simp_rw [update_self]; exact hE.mono fun i hi=>hi.frame.align
     simp_rw [update_of_ne he]; exact hA' d
  have hx:= neighboring F (observes F H X hX) ha
  refine ⟨fun i=> compatible F (A' i),localCost_trans ha (fun d=> fitted_up F hx d), ?_,plan_angle F h H hx hu, fun d e he=> accounted F d e he hx⟩
  filter_upwards [unchanged4 F h H hx (fun d _=> hu d),hP₁] with i he hI; rw [he]; simpa only [A',update_self]
end YM.PhysMS.Frame
