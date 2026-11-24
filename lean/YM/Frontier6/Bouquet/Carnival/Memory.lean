import YM.Frontier6.Bouquet.Carnival.MainRing
/-! The root sum with error ledger. Ranks.N tested orders independent of carrier
 epsilon, audience and clocks. Main root only when >1, proper rule at any root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable (K:Final C F S){P:Ensemble}(d:Slot →ℕ)(v:(j:Slot)→ S.Field (d j))(i:P) (p:Part d i) (M:Pod→ℝ) (R: Air (S:=S) P I L Y){B C' ε δ D:ℝ}{n:ℕ}

lemma legends (h:Dais K d P M)(he: R.Welkin M) (hv:1< i.val.card) {x:I} {s a:ℝ}{f:Full (fiber P)}(hh: Length P M s)(hf: Fair f (R.region x).foot (R.region x).center):
   launch K d v (R.region x) (R.sky x) s a f=∑ p:Part d i, ∑' j:ℕ,titled K d v i p R s a (Normal.pitch j) x f:=by
       simp_rw [← ann_play K d v i _ _ _ he h hh hf]; rw [Fintype.sum_option]; exact seesaw K _ _ i d s _ _ _ (continuation K _ d v s _ hv hh.pos (card_allowed h hh i)) (auditions i h (he.safe _) hh hf (he.smooth _))
lemma rhythms {F:ℕ→Y} {s:ℝ}(he:0<s)(h:∀ i:ℕ, ‖F i‖≤ Rhythm ε (Normal.pitch i/s)*B): Rates ε ε s B F:=by
   constructor
   · intro i hi; rw [← rhythm_up ((div_le_one he).2 hi)]; exact h i
   intro i hi; rw [← inv_div,← Real.rpow_neg_eq_inv_rpow,← rhythm_down ((one_le_div he).2 hi)]; exact h i
abbrev claim (s a:ℝ)(x:I)(f:Full (fiber P))(j:ℕ):= titled K d v i p R s a (Normal.pitch j) x f
section
variable {K d v i p M R}(h:Announces K d v i p M R B C' n ε δ D)(he:R.Welkin M)
variable (hδ:0<δ) {Z:ℝ} (ht:∀ t A:ℝ,0<t→0≤A→∀ g:ℕ→ Y, Rates δ δ t A g → Mass g (Z*A))
variable {x:I}{f:Full (fiber P)}{s a b U:ℝ}(ha:0<a)(hl:Length P M s)(hp:R.suitable x C' s)(hv:Fellow P (R.lengths x) (R.region x) B f n U)
include h he ht ha hl hp hv
lemma Announces.grants : Mass (claim K d v i p R s a x f) (Z*(D*U*R.freight d x ε)):= ht _ _ (R.length_pos ..) (mul_nonneg (mul_nonneg h.pos hv.costs.nonneg) (R.freight_pos d he _ _).le) _ (rhythms (R.length_pos ..) (fun j=> h.keep x f s a (Normal.pitch j) U ha hl (pitches _) (pitch_le _) hp hv))
lemma Announces.amass (hh:a≤b) : Mass (fun j:ℕ=> claim K d v i p R s a x f j - claim K d v i p R s b x f j) (Z*(D*U*R.freight d x ε*R.delta x b)):= ht (R.lengths x i) _ (R.length_pos ..) (mul_nonneg (mul_nonneg (mul_nonneg h.pos hv.costs.nonneg) (R.freight_pos d he _ _).le) (R.delta_pos _ (ha.trans_le hh)).le) _ (rhythms (R.length_pos ..) (fun j=> (h.continuousUp x f s a b (Normal.pitch j) U ha hh hl (pitches _) (pitch_le _) hp hv).trans_eq (mul_assoc ..)))
end
section
variable {M R} (h:Seated K d v i n) (hc:1< i.val.card)
include h hc
lemma launch_bounds {B C' ε:ℝ}{m:ℕ}(hB:1≤ B)(hC:1≤C')(hε:0<ε)(ht:Dais K d P M)(he:R.Welkin M)(hp:Air.Hosts K R)(hD:∀ z:Part d i,n+toil i z n ≤ m):∃ D:ℝ,Endows K d v P M R m B C' ε D:=by
   let δ:=min (ε/2) (1/4); have hh:0<δ:= lt_min (half_pos hε) (by norm_num); choose V hV using (fun p:Part d i=> winnings K d v i p M R B C' n he ht hp h hB hC hh (min_le_right ..) (ε:=ε) (by unfold δ; linarith only [min_le_left (ε/2) (1/4)])); obtain ⟨Z,hZ,hM⟩:= cascade (Y:=Y) δ δ hh hh; let D:=∑ p:Part d i,Z*V p; have hz:0≤ D:= Finset.sum_nonneg (fun j _=>mul_nonneg hZ (hV j).pos)
   let F(x:I)(f:Full (fiber P))(p:Part d i)(s a:ℝ):= claim K d v i p R s a x f
   have hF(p:Part d i){x:I}{f:Full (fiber P)}{s a U:ℝ} (h:0<a)(hh:Length P M s)(hp:R.suitable x C' s)(he':Fellow P (R.lengths x) (R.region x) B f m U): Mass (F x f p s a) (Z*(V p*U*R.freight d x ε)) := (hV p).grants he hM h hh hp (he'.below (hD p) le_rfl)
   have hy(x:I)(U:ℝ): D*U*R.account x * stars d P (R.lengths x) * R.route.ruin x ε= ∑ p:Part d i,Z*(V p*U * R.freight d x ε):=by unfold D; simp_rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro _ _; unfold Air.freight; ring
   refine ⟨D,hz,fun x U s a f ha hl hp hh =>?_,fun x U s a b f ha hb hl hp hh=>?_⟩
   · change ‖launch ..‖ ≤ _; rw [legends K d v i M R ht he hc hl hh.fair,hy]; exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun p _=> (hF p ha hl hp hh).total))
   change ‖uKernel _ _ _ _ _ _ _ _ _-uKernel _ _ _ _ _ _ _ _ _‖ ≤ _; let V':= ∑ p:Part d i,∑' j,(F x f p s a j - F x f p s b j); have h': launch K d v (R.region x) (R.sky x) s a f-launch K d v (R.region x) (R.sky x) s b f=V':=by rw [legends K d v i M R ht he hc hl hh.fair,legends K d v i M R ht he hc hl hh.fair,← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun p _=> ((hF p ha hl hp hh).sums.tsum_sub (hF p (ha.trans_le hb) hl hp hh).sums).symm)
   unfold launch at h'; rw [h',hy,Finset.sum_mul]; exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun p _=> ((hV p).amass he hM ha hl hp (hh.below (hD p) le_rfl) hb).total.trans_eq (mul_assoc ..).symm)) -- delta

lemma joins : ∃ m,Sails K d v P m:=by
   obtain ⟨m,hm⟩ : ∃ m:ℕ,∀ p:Part d i,n+toil i p n ≤ m:= (eventually_all.mpr (fun p:Part d i=> eventually_ge_atTop _)).exists; exact ⟨m,fun ht he hp B C ε hB hC hε=> launch_bounds K d v i h hc hB hC hε ht he hp hm⟩
end
end YM.Frontier6.Bouquet.Atelier
