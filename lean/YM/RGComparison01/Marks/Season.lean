import YM.RGComparison01.Marks.Checks
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Season
open Foreman Checks Baked Palette Resin Pillow Selector March Opacity
variable {M:ι→Leaf R} {ρ:ι→ℝ} {z: Cl M H}
-- distinguished E assigned no boosts in Team pricing. Only E for inherited when NOT a Leaf
abbrev sand (p:Cake M H):= p.1.val \ p.2.reach
def ocean (Ψ:ℕ→Prop)(p:Cake M H) := ∃ k, Ψ k ∧ Opacity.key S k ∈ sand p
def scare (p:Cake M H):= ∃ i∈ sand p, JOB S i
abbrev Ode (Ψ:ℕ→Prop)(p:Cl M H) := ∃ i, ocean Ψ (p.2 i)
def age (z:Cl M H):= ∑ i,(sand (z.2 i)).card
def often (z:Cl M H):= ∑ i,Cash.numP (z.2 i).1.val
def drift (z:Cl M H):= ∑ i,H.shapeW (z.2 i).1.val
abbrev Heavy (n:ℕ)(z:Cl M H):= n ≤ age z ∨ 1 ≤ often z ∨ (radiusB s:ℝ) ≤ drift z ∨ ∃ i, scare (z.2 i)
-- keep arity total when only squarefree jobs
abbrev allot (z:Cl M H):= ∑ i,(z.2 i).2.val.card
variable (hD: 1 ≤ D) (ht:1 ≤ t) (h:1 ≤ D')

def ledgerP (v : Cake M H)(Ψ: ℕ→Prop)(D t D':ℝ) := (∏ i∈sand v, freight Ψ D t D' i)

def trove (z : Cl M H)(Ψ:ℕ→Prop) (D t D':ℝ) := Baked.weight M (fun v=> sheen M v Ψ D t D') z
local notation "E'" => Q.mark L μ s
lemma treasure (z:Cl M H) : trove z Ψ D t D'= (∏ i,ledgerP (z.2 i) Ψ D t D') * Real.exp (E' * often z) * Real.exp (Q.ε * drift z):=by
   unfold trove Baked.weight sheen; rw [prod_mul_distrib, prod_mul_distrib]; simp only [← Real.exp_sum,← mul_sum,often,drift,Nat.cast_sum]; rfl
include hD ht h
lemma safe (z:Cl M H): 1 ≤ trove z Ψ D t D':= one_le_prod fun _ _=> sheen_paid M _ hD ht h
lemma worth (p:Cake M H): 1 ≤ ledgerP p Ψ D t D' := one_le_prod fun _ _=> stock_ge hD ht h _
lemma in_set (z:Cl M H)(p)(i:Head S)(ht':i ∈ sand (z.2 p)): freight Ψ D t D' i ≤ trove z Ψ D t D':= by
   have hw {ι: Type} [DecidableEq ι] (f:ι→ℝ) {U':Finset ι} (hp : ∀ i∈U',1≤f i) (i:ι) (h:i∈U') : f i≤∏ i∈ U',f i:= by
     rw [← Finset.prod_singleton f]; exact Finset.prod_le_prod_of_subset_of_one_le
      (Finset.singleton_subset_iff.mpr h) (fun _ hh=>zero_le_one.trans (hp _ ((Finset.singleton_subset_iff.mpr h) hh))) (fun _ hh _=> hp _ hh)
   have he' : 0 ≤ E' := H.laws.acquired.marked
   rw [treasure]; apply le_trans (hw (U':=sand (z.2 p)) _ (fun i _=> stock_ge hD ht h _) i ht')
   let X: ℝ:= ∏ i,ledgerP (z.2 i) Ψ D t D'; have hh i : 1 ≤ ledgerP (z.2 i) Ψ D t D' := worth hD ht h _
   have hx : 1 ≤ X:= one_le_prod fun i _=> hh i
   refine le_trans (b:=X) (hw _ (fun i _=> hh i) p (mem_univ _)) ?_
   have hM: 1 ≤ Real.exp (E'* often z):=Real.one_le_exp (mul_nonneg he' (Nat.cast_nonneg _))
   exact (le_mul_of_one_le_right (zero_le_one.trans hx) hM).trans (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hx hM)) (Real.one_le_exp (mul_nonneg Q.usable.le (Finset.sum_nonneg fun _ _=> H.positive_volume _))))

lemma oasis (hO: Ode Ψ z) : D ≤ trove z Ψ D t D':= by
   obtain ⟨i,n,hx,hp⟩:=hO; exact le_trans (le_of_eq (show freight Ψ D t D' (Opacity.key S n)=D from if_pos hx).symm) (in_set hD ht h z i _ hp)
omit hD in
lemma shallows (p:Cake M H)(he : ¬ocean Ψ p)(i : Head S)(hp:i∈ sand p): t ≤ freight Ψ D t D' i:= by
    unfold freight; split
    next t=> rw [if_neg (fun hv=>he ⟨t,hv,hp⟩)]
    next=> exact le_mul_of_one_le_left (zero_le_one.trans ht) (policy_ge _ _ h (fun _=> le_rfl) _)

lemma wealth (hH : Heavy k z) (hp:¬ Ode Ψ z) {v:ℝ} (hz:v ≤ t^k)(hf:v ≤ D') (hs:v ≤ Real.exp E') (hq : v ≤ Real.exp (Q.ε*radiusB s)) : v ≤ trove z Ψ D t D':= by
   have hM:0 ≤ E':= H.laws.acquired.marked; have hv0: 1 ≤ Real.exp (E' * often z) := Real.one_le_exp (mul_nonneg hM (by positivity)); have hw': 1 ≤ Real.exp (Q.ε*drift z) := Real.one_le_exp (mul_nonneg Q.usable.le (Finset.sum_nonneg fun _ _=> H.positive_volume _));
   let w i:=ledgerP (z.2 i) Ψ D t D'; have hw i:1 ≤ w i:= worth hD ht h _; have hX : 1 ≤ ∏ i,w i:= one_le_prod fun _ _=> hw _
   rcases hH with hH|hH|hH|⟨i,j,hj,hi⟩
   · rw [treasure]; apply hz.trans
     refine le_trans (pow_le_pow_right₀ ht hH) ((le_trans (b:=∏ i,w i) ?_ ((le_mul_of_one_le_right (zero_le_one.trans hX) hv0).trans (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hX hv0)) hw'))))
     unfold age; rw [← Finset.prod_pow_eq_pow_sum]; refine prod_le_prod (fun i _=> pow_nonneg (zero_le_one.trans ht) _) fun i _=> ?_; rw [← Finset.prod_const]; exact prod_le_prod (fun _ _=> zero_le_one.trans ht) (fun j hj=> shallows ht h _ (fun h=> hp ⟨i,h⟩) j hj)
   · rw [treasure]; exact hs.trans ((Real.exp_monotone (le_mul_of_one_le_right hM (by exact_mod_cast hH))).trans ((le_mul_of_one_le_left (Real.exp_nonneg _) hX).trans (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hX hv0)) hw')))
   · rw [treasure]; exact hq.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left hH Q.usable.le)).trans (le_mul_of_one_le_left (Real.exp_nonneg _) (one_le_mul_of_one_le_of_one_le hX hv0)))
   apply hf.trans; apply le_trans _ (in_set hD ht h z i _ hj); unfold freight; split
   next j=> exact False.elim ((by
      have hm := hi (fun _=>1) 0; have hv : policyP (S:=S) (fun _=>1) 0 (Opacity.key S j)= 1:=rfl
      exact one_ne_zero (hv.symm.trans hm)))
   next j=> have hw:= (show JOB S _ from hi) (fun _=>1) D'; rw [hw]; exact le_mul_of_one_le_right (zero_le_one.trans h) ht
end Season
end YM.RGComparison01.Pledge
