import YM.OPE.Compatible.Soup.Yen
import YM.OPE.Compatible.Porch.Bush
/-!
# Sparse total costs. Alphabet earns analytic derivatives, pay summable in all n.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
variable {G:Gauge}{b i j k r:ℕ}{n:Side}
variable {v s a c:ℝ}{p:Clip}{Z:PathData G}
open Next.Free Next.Scheduling
-- all scaled budgeted tangent stacks. s>0 small
noncomputable def knotter (b:ℕ)(s:ℝ)(i:Site n):ℝ:=Real.exp (-s*↑(pdist i-b)) -- cast explicit subtract nat?
lemma knotPos (s:ℝ)(b:ℕ)(i:Site n):0<knotter b s i:=Real.exp_pos _
lemma knotLow (hs:0 < s)(b:ℕ)(x:Site n):knotter b s x ≤ 1:= Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (Nat.cast_nonneg _))
noncomputable def Squad(b:ℕ)(s:ℝ):ℝ:= (2*(b+1):ℝ)^ (4:ℕ) * ∑' j, Next.Scheduling.decay 4 s j
lemma knot_sum (n:Side)(b:ℕ)(hs:0<s):∑ i:Site n,knotter b s i≤ Squad b s:=by
        let U(j):=Next.Scheduling.decay 4 s j; let h(i: Site n):=pdist i-b; let c := (2*(b+1):ℝ); let C :=c^4; have hu(j):0 ≤ U j:=by unfold U Next.Scheduling.decay; positivity
        have he : SumBudget U (∑' i,U i):=⟨hu,decay_summable 4 s hs,le_rfl⟩; have hs': SumBudget (knotter b s (n:=n)) (C*∑' i,U i):=by
              apply budget_fiberwise h (fun i=> (knotPos s b i).le) _ (budget_scale (x:=C) (by unfold C; positivity) he)
              intro i S hS; have ht : S⊆ berth (b+i):=fun x hx=>by have he:= hS x hx; unfold h at he; exact (berthH x).mpr (by omega)
              have hr:(↑S.card :ℝ) ≤ C*((i:ℝ)+1)^(4:ℕ):=by
                 apply le_trans (Nat.cast_le.mpr ((card_le_card ht).trans (cardinal_B n))) _; unfold C c; rw [←mul_pow];push_cast; gcongr; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) b) (Nat.cast_nonneg (α:=ℝ) i)]
              let P:= Real.exp (-s*i); rw [sum_congr rfl (show ∀ x∈ S,knotter b s x=P from fun x hx=>by change Real.exp (-s*↑(h x))= P; rw [hS x hx]),sum_const,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le).trans_eq (by unfold U Next.Scheduling.decay; ring)
        simpa only [Squad,tsum_fintype] using hs'.2.2 -- unfold C etc
-- full tangent. cliff for all
abbrev SerT (V:Bid.Dir G n)(b:ℕ):Prop:=∀ e,V (arkE e)≠0 → pdist e.1 ≤ b∧pdist (dotUp e) ≤ b
lemma SerT.raise {V:Bid.Dir G n}(h:SerT V b)(he:b ≤ i): SerT V i:=fun j hj=> ⟨(h j hj).1.trans he,(h j hj).2.trans he⟩
lemma SerT.plus {V Y:Bid.Dir G n}(h:SerT V b)(hv:SerT Y b):SerT (V+Y) b:=fun e he=>by by_cases hp:V (arkE e)≠0; exact h _ hp; apply hv _ (fun hx=>he (by rw [Pi.add_apply,hx,not_not.mp hp,zero_add]))
lemma SerT.gauge {V:Bid.Dir G n}(h:SerT V b)(v:ℝ): SerT (v • V) b:=fun i hi=> h _ (fun he=> hi (by rw[Pi.smul_apply,he,smul_zero]))
lemma SerT.actual {V:Bid.Dir G n}(h:SerT V b): Toss (represent V) b:=fun e he=> h _ (fun hh=> he (by rw [arkL,hh,G.mat_lieExp_zero]))
open Libra.Shell Libra.Char
lemma SerT.tar {V:Bid.Dir G n}(h:SerT V b)(hx:‖V‖ < c)(q:Site n)(hs:0<s): twigK (upl q (spool G n V)) (c*knotter b s q) s:=by
      have hc: 0<c:=(norm_nonneg _).trans_lt hx; refine ⟨mul_pos hc (knotPos s b q),fun i=>?_⟩; let y:= q+wrap n i.1; let e: Edge (Site n):=(y,i.2); rw [show indexS i (upl q (spool G n V))=V (arkE e) from rfl]; by_cases he: V (arkE e)≠ 0
      · have hp:= (h e he).1; change pdist y ≤ b at hp; have ht: pdist q ≤ b+size i.1:=by
              have hx:pdist (wrap n i.1)≤ size i.1:= within_size ..; have hz:= sepK q y; rw [separation_comm,separation, show y-q=wrap n i.1 from add_sub_cancel_left ..] at hz; omega
        apply (norm_le_pi_norm V _).trans; apply hx.le.trans; rw [mul_assoc,knotter,← Real.exp_add]; exact le_mul_of_one_le_right hc.le (Real.one_le_exp (by rw [neg_mul]; have hz:= mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr (show pdist q-b ≤ size i.1 from by omega)) hs.le; linarith only [hz]))
      rw [not_not.mp he,norm_zero]; exact (mul_pos (mul_pos hc (knotPos s b q)) (Real.exp_pos _)).le
variable (X:Bid.Dir G n)
lemma seren (p:CoverConfig G→ℝ)(he:seedD p s k a)(ha:0≤a)(h:SerT X b)(hc:‖X‖ < c)(hs:0<s):let f:= fun t:ℝ=>waterV p (represent (t • X)); ContDiff ℝ ∞ f∧∀ i:ℕ, 0 < i →  i ≤ k → ∀ t:ℝ, ‖iteratedDeriv i f t‖ ≤ a*c^i*Squad b s:=by
        let v(i:Site n):= upl i (spool G n X); let g(i:Site n)(t:ℝ):=p (lotU (t • v i)); intro f; have hf : f = ∑ i,g i:=by funext t; rw [Finset.sum_apply]; exact sum_congr rfl (fun i _=>congr_arg p (by rw [← Grid.plank,map_smul]; rfl))
        have hh(i): Quiet (v i) 0:=Silt.Phere.rayQuiet i X; have ht(i):= he (v i) (hh i) _ (h.tar hc i hs); rw [hf]; refine ⟨(by rw [show (∑ i,g i)=fun t=>∑ i,g i t from funext fun t=> Finset.sum_apply ..]; exact ContDiff.sum fun i _=> (ht i).1),fun i hi hI t=>?_⟩; rw [show iteratedDeriv i (∑ i,g i) t=∑ j,iteratedDeriv i (g j) t from ?_]; swap
        · apply iteratedDeriv_sum; intro i hv; exact (((ht i).1).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
        have hp:0 ≤ c:= (norm_nonneg X).trans hc.le; apply (norm_sum_le ..).trans; refine le_trans (sum_le_sum (g:=fun j=> a*c^i*knotter b s j) (fun j _=> ?_)) ?_; rotate_left
        · rw[← mul_sum]; exact mul_le_mul_of_nonneg_left (knot_sum n b hs) (mul_nonneg ha (pow_nonneg hp _))
        apply ((ht j).2 i hI t).trans; rw[mul_pow,← mul_assoc]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg ha (pow_nonneg hp _)); calc
             _ ≤ knotter b s j^1:=pow_le_pow_of_le_one (knotPos _ _ _).le (knotLow hs ..) hi
             _ = _:=pow_one _
end YM.OPE.Merchant.Aloof
