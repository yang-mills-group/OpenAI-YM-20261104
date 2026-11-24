import YM.OPE.Samples.Frame
/-!
# Seat declarations for axes and grid snap

A leader as a function of leaf key and current season. Moves only at
its debut. For every season arrange distinct leaders in every coordinate. This
includes distinction from virtual leader. At final resolution the descendants
within the declared leader remain within their narrow bandwidth. Every pair
of leaves therefore automatically has strict separation *in every coordinate*
at the final level. No tie between copies of a partially substituted (redacted)
frame and a surviving cluster leaf. No guard of any other form is needed
against vanishing components of moments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter MeasureTheory Lattice RG Wilson Polar Rhythm Border
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C: Family G}{I L J:Type}[Fintype I][DecidableEq I]{i j k:I}{Q:Rhythm I} {H t u v w n A:ℕ} {f:Filter L} {X:L→ I→E4}
    {T:L→ℝ}{R r s: L→ℕ→ℝ} {α:ℕ→ℝ}{q e a b : L→ℝ}{M η:ℝ} {x: I→ E4} {δ s' :ℕ→ ℝ}
set_option quotPrecheck false
local notation "μ"=> C.S.a
local notation "σ"=> (fun i=> C.path.levels.budget i)
local notation "U"=> Q.localTime H
variable {S:Loom Q}
structure Seated (Q:Rhythm I)(C:Family G)(S:Q.Loom)(x:I→ E4)(H:ℕ) : Prop where
    aligned i: Travel C.S (S.launch (Q.localTime H i)) (Q.stroke H x i)
    clears i a: Q.stroke H x i a ≠ 0
    siblings i j:i≠j→ Q.localTime H i=Q.localTime H j → ∀ a,Q.stroke H x i a≠ Q.stroke H x j a
namespace Seated
variable (W:Seated Q C S x H)(hh:H ≤ Q.age Q.star)
local notation "P'"=> Q.point H x
include hh W
lemma provenance (i:I): Travel C.S (S.launch (U i)) (x i) := by
    generalize hy:U i = n; induction n using Nat.strong_induction_on generalizing i with | h n ih=>
    by_cases hc: Q.pinned H i n
    · have hx:Q.stroke H x i=x i:=(by unfold stroke; rw [hy,Q.lead_zero hc _,sub_zero]); rw [← hy,← hx]; exact W.aligned _
    let j:= Q.chief i n; have hn: U j<n:= Q.leadMom hh hc; have he:n ≤ Q.limit:= hy ▸ (Q.timeBirth hh i).trans (Q.bounded _); have ht:Q.stroke H x i+x j=x i:= by unfold stroke; rw [hy,point,if_neg hc]; exact sub_add_cancel ..
    exact ht ▸ Travel.add (hy ▸ W.aligned i) ((ih _ hn j rfl).inh (S.mono Q hn.le he))
lemma neverMind (he:t ≤ Q.limit): Travel C.S (priorL S t) (P' i t):= by
    by_cases h: Q.pinned H i t; · rw [Q.lead_zero h]; exact Travel.null
    have hp:=Q.leadMom hh h; unfold point priorL; rw [if_neg (show t≠0 from (by omega)),if_neg h]; exact (W.provenance hh _).inh (S.mono Q (by omega) (le_trans (by omega : t-1 ≤ t) he))
lemma focusBounds (h:t ≤ Q.limit)(i:I): Travel C.S (S.launch t) (P' i (t+1)):=by
    by_cases hc: Q.pinned H i (t+1); · rw [Q.lead_zero hc]; exact Travel.null
    unfold point; rw [if_neg hc]; exact (W.provenance hh _).inh (S.mono Q (Nat.le_of_lt_succ (Q.leadMom hh hc)) h)
-- orientation.Motion disparity. If not leader of parent and current leader distinct then offset has own index
lemma forks (he:Q.phase t i j)(ht:¬Q.phase (t+1) i j) : ∀ d,P' i (t+1) d≠ P' j (t+1) d :=by
    have hz{u v:I}(he: Q.phase t u v)(ht: ¬ Q.phase (t+1) u v)(hp:Q.pinned H u (t+1)): ∀ a,P' u (t+1) a≠ P' v (t+1) a:=by
       let l:=t+1; have hv:¬Q.pinned H v l:= fun h=> ht (Q.conj (Q.swap (Q.on_focus|>.1 hp.2)) (Q.on_focus|>.1 h.2)); let k:=Q.chief v l; have he':Q.pinned H k t:= Q.pinSame hp (Nat.le_succ t) (Q.conj he (Q.phase_low (Q.matchs v l) (Nat.le_succ _))); have hk: U k=t:=Q.debut hh (Q.continue_leader hv) (fun h=> h.1 he')
       intro a; rw [Q.lead_zero hp, point,if_neg hv]; exact (show x k a≠0 from (by have H:= W.clears k a; unfold stroke at H; rwa [hk,Q.lead_zero he',sub_zero] at H)).symm
    let m:= t+1; let a:=Q.chief i m; let b':= Q.chief j m; by_cases ha:Q.pinned H i m; · exact hz he ht ha
    by_cases hb:Q.pinned H j m; · exact fun d=> (hz (Q.swap he) (fun h=> ht (Q.swap h)) hb d).symm
    have hab: a≠ b':= fun h=> ht ((Q.agrees ..).1 h); have hA:=Q.clocked hh|>.1 (Q.continue_leader ha); have hB:=Q.clocked hh|>.1 (Q.continue_leader hb); change U a < t+1 at hA; change U b'<t+1 at hB
    intro d; unfold point; rw [if_neg ha,if_neg hb]; change x a d≠x b' d
    have H':Q.phase t a b':= Q.conj (Q.phase_low (Q.swap (Q.matchs ..)) (Nat.le_succ _)) (Q.conj he (Q.phase_low (Q.matchs ..) (Nat.le_succ _))); have H₀: P' a t=P' b' t:= Q.lead_eq H' _
    have hv(k k':I)(ht:P' k t=P' k' t)(hh':U k=t)(hn: U k'<t): x k d≠x k' d:=by
       intro h; apply W.clears k d; unfold stroke; rw [hh',ht,Q.lead_at ((Q.clocked hh).2 hn), PiLp.sub_apply,h, sub_self]
    rcases lt_or_ge (U a) t with h|h <;> rcases lt_or_ge (U b') t with hp|hp
    · exact (hab ((((Q.clocked hh).2 h).2.symm.trans ((Q.chiefFor H').trans (((Q.clocked hh).2 hp).2))))).elim -- define
    · exact (hv b' a H₀.symm (by omega) h).symm
    · exact hv a b' H₀ (by omega) hp
    have H1 : U a=t:=(by omega); have H2: U b'=t:=by omega
    intro W'; have he:= W.siblings a b' hab (H1.trans H2.symm) d; apply he; unfold stroke; rw [H1,H2,H₀,PiLp.sub_apply,PiLp.sub_apply,W']
-- every gap ≥ mesh
omit hh W
private lemma lies {α β:E4}{q:ℕ} {d:Axis}(hα:Travel C.S q α)(hβ:Travel C.S q β)(ht:α d≠ β d): μ q≤ ‖(α-β) d‖:=by
    obtain ⟨u,rfl⟩:=hα; obtain ⟨v,rfl⟩:=hβ; have he : u d≠v d:= fun he=> ht (congr_arg (fun x:ℤ=> μ q * x) he); have hv: (1:ℝ)≤ |(((u-v) d:ℤ):ℝ)|:=by
       exact_mod_cast (show (1:ℤ) ≤ |(u-v) d| from abs_pos.mpr (sub_ne_zero.mpr he)) -- int pos mix
    change μ q≤ ‖ μ q*u d-μ q*v d‖; rw [← mul_sub,norm_mul,Real.norm_of_nonneg (C.S.a_pos _).le]; exact le_mul_of_one_le_right (C.S.a_pos _|>.le) (by change (1:ℝ)≤ |(u d:ℝ)-v d|; simpa using hv)
include hh W
lemma splitPorts (he:Q.phase t i j)(ht:¬Q.phase (t+1) i j)(hp:t ≤ Q.limit)(d:Axis): μ (S.launch t) ≤ ‖P' i (t+1) d-P' j (t+1) d‖:= lies (W.focusBounds hh hp i) (W.focusBounds hh hp j) (W.forks hh he ht d)
lemma seenParts (he:i≠j) (ht:t=Q.gap i j)(hv:4*‖x i-P' i (t+1)‖< μ (S.launch t))(hq:4*‖x j-P' j (t+1)‖< μ (S.launch t))(d:Axis): x i d≠x j d:=by
    subst t; let t:= Q.gap i j; let a:= P' i (t+1); let b:= P' j (t+1); intro h
    have hx:=W.splitPorts hh (t:=Q.gap i j) (Or.inr le_rfl) (fun h=> Nat.lt_succ_self t|>.not_ge ((Q.split he).1 h)) (GapHomebound i j) d
    let v:= x i; let u:= x j; have hA : 4*‖v d-a d‖ < μ (S.launch t):= lt_of_le_of_lt (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (v-a) d) (by norm_num)) hv; have hB : 4*‖u d-b d‖< μ (S.launch t):= lt_of_le_of_lt (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (u-b) d) (by norm_num)) hq
    have hh : ‖a d-b d‖≤ ‖v d-a d‖+ ‖u d-b d‖:=by rw [norm_sub_rev (v d),show u d=v d from h.symm]; simpa [dist_eq_norm] using dist_triangle (a d) (v d) (b d) -- lemma
    linarith only [hx,hA,hB,hh,C.S.a_pos (S.launch t)]
lemma virtualSplit (he:i∉ Q.focus H) (hk:t=Q.gap Q.star i)(hp:t<H)(hv:4*‖x i-P' i (t+1)‖< μ (S.launch t))(d:Axis): x i d ≠ 0:=by
    let hH: H≤ Q.limit:= hh.trans (Q.bounded _); have he':Q.star≠ i:= fun h=> he (h ▸ (Q.on_focus).2 (Q.yes ..)); intro h; let a:= P' i (t+1); have hh : P' Q.star (t+1)=0:= Q.lead_zero (show Q.pinned H Q.star (t+1) from ⟨hp,(Q.on_focus).2 (Q.yes ..)⟩) _;
    have hu:= W.splitPorts ‹H ≤ Q.age Q.star› (i:=Q.star) (j:=i) (t:=t) (Or.inr hk.le) (fun H'=> (Nat.lt_succ_self t|>.not_ge (((Q.split he').1 H').trans hk.ge))) (hp.le.trans hH) d
    have hA: 4* ‖x i d-a d‖< μ (S.launch t):= lt_of_le_of_lt (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (x i-a) d) (by norm_num)) hv
    rw [hh] at hu; rw [h] at hA; change μ (S.launch t) ≤ ‖0 - a d‖ at hu; linarith only [hA,hu,C.S.a_pos (S.launch t)]
end Seated
end YM.OPE.Log.Trunk
