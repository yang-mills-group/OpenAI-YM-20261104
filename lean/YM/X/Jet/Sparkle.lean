import YM.X.Jet.Reach
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
/-!
# Formal scalar substitution in word jets. Faa di Bruno makes it usable even for nonnormed vector streams. No convergence of series. analytic realization finite.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Jet
open Function Filter Set
open scoped Topology ContDiff BigOperators Classical
universe u v w
variable {V:Type u}{I:Type v} {n i j k:ℕ}
local notation "S"=> Word ℝ
abbrev light (a:S): Prop:=a 0=0
abbrev fitto (p q:Word V)(n:ℕ):Prop:=∀ i≤n,p i=q i
-- type0 unbounded algebra.V; Γ weights use x0 ignored.
section
variable [AddCommMonoid V][Module ℝ V]
def order (p: OrderedFinpartition i)(x:Word ℝ)(v:Word V):V:= (∏ j,(p.partSize j).factorial * x (p.partSize j):ℝ) • ((p.length.factorial:ℝ) • v p.length) -- nat casts
-- when not light, treats as x0=0.
def ren (x:S)(p:Word V)(i:ℕ):V:= ((i.factorial:ℝ))⁻¹ • ∑ t:OrderedFinpartition i, order t x p
variable {x y:S}{p q:Word V}
lemma ren_writes {W:Type v} [AddCommMonoid W][Module ℝ W] (a:V→ₗ[ℝ] W)(x:S)(p:Word V): a ∘ ren x p=ren x (a ∘ p):= by ext1 i; unfold ren order; simp only [comp_apply,map_smul,map_sum]
lemma ren_add : ren x (p+q)=ren x p+ren x q:=by funext i; unfold ren order; simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
lemma price_p (h:fitto p q n)(hx:fitto x y n) : fitto (ren x p) (ren y q) n:= by
     intro i hi; unfold ren; apply congr_arg; refine Finset.sum_congr rfl fun t _=> ?_ ; unfold order; rw [h _ (t.length_le.trans hi)]; apply congr_arg (· • _); apply Finset.prod_congr rfl; intro j _; rw [hx _ ((t.partSize_le j).trans hi)]
end
section
variable {x y:S}{q':ℝ→ℝ} {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{p q:Word V}{f' : ℝ→V}
lemma eo_Act (a:ℕ)(h:ContDiffAt ℝ ω f' 0): Act a f' (someJ f'):= ⟨h,fun _ _=>rfl⟩
lemma Act.dial (h:Act n q' x) (hp:Act n f' p)(hl:light x) : Act n (f' ∘ q') (ren x p):= by
    have he:q' 0=0:= h.zero.trans hl; have hh:ContDiffAt ℝ ω f' (q' 0):= by rw [he]; exact hp.nice
    refine ⟨hh.comp _ h.nice,fun i hi=>?_⟩; unfold someJ ren; apply congr_arg; rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hh h.nice le_top]; apply Finset.sum_congr rfl; intro t _; rw [he,hp.actual _ (t.length_le.trans hi)]; unfold order; apply congr_arg (· • _); apply Finset.prod_congr rfl; intro j _; exact h.actual (t.partSize j) ((t.partSize_le j).trans hi)
lemma ren_light (h:light x)(v:Word V) : ren x v 0=v 0:= by
   let g:=delay x 0; let f:= delay v 0; have he : Act 0 (f ∘ g) (ren x v):=(Act.swell x le_rfl).dial (Act.swell v le_rfl) h; exact he.zero.symm.trans (Eq.trans (congr_arg f ((delay_zero x 0).trans h)) (delay_zero v 0))
lemma voyage (a: ℝ→V) : someJ a 1=deriv a 0:= by simp [someJ]
lemma Act.first (h:Act n f' p)(he:1≤n) : HasDerivAt f' (p 1) 0:= by rw [← h.writes 1 he,voyage]; exact (h.nice.differentiableAt (by simp)).hasDerivAt
lemma tip (h:light x) (v:Word V): ren x v 1=x 1 • v 1:= by
   let f:=delay x 1; let g:=delay v 1; have hx: Act 1 f x:= Act.swell x le_rfl; have hv: Act 1 g v:= Act.swell v le_rfl; have hg: HasDerivAt g (v 1) (f 0):=by rw [hx.zero.trans h]; exact hv.first le_rfl
   exact ((hx.dial hv h).first le_rfl).unique (hg.scomp _ (hx.first le_rfl)) -- norm multicore
lemma asc (h:light x)(g:light y)(a:Word V): ren x (ren y a)= ren (ren x y) a:= by
   funext i; let f:=Act.swell x (show i ≤ i from le_rfl); let p:=Act.swell y (show i ≤ i from le_rfl); let c:=Act.swell a (show i ≤ i from le_rfl)
   exact (f.dial (p.dial c g) h).trans_at ((f.dial p h).dial c ((ren_light h y).trans g)) le_rfl
-- general Jet in e≥ concerns.Work.Calibration.Alternative
lemma run_ren {E:Type v}[NormedAddCommGroup E][NormedSpace ℝ E](f:V→E)(p:Word V)(h:light x)(hf:ContDiffAt ℝ ω f (p 0)): run f (ren x p)= ren x (run f p):= by
   funext i; have hv:= Act.swell p (show i ≤ i from le_rfl); have hx:=Act.swell x (show i ≤ i from le_rfl); refine ((hx.dial hv h).transit (by rw [ren_light h]; exact hf)).trans_at (hx.dial (hv.transit hf) h) le_rfl
-- compatibility with formal frame parity
lemma ren_turn_x (p:Word V)(h:light x): ren (turn x) p=turn (ren x p):= by
    funext i; have H:=Act.swell x (show i ≤ i from le_rfl); let T:=Act.swell p (show i ≤ i from le_rfl); exact (H.reflects.dial T (turn_zero _|>.trans h)).trans_at (H.dial T h).reflects le_rfl
lemma ren_turn_v (p:Word V)(h:light x): ren x (turn p)=ren (-x) p:= by
    funext i; have H:=Act.swell x (show i ≤ i from le_rfl); have hv: Act i (fun t=> -delay x i t) (-x):= by simpa using! H.smul (-1)
    let T:=Act.swell p (show i ≤ i from le_rfl); exact (H.dial T.reflects h).trans_at (hv.dial T (by unfold light;simp [show x 0=0 from h])) le_rfl
lemma ren_static (p:V)(h:light x): ren x (just p)=just p:= by ext1 i; exact ((Act.swell x (show i ≤ i from le_rfl)).dial (Act.static p) h).trans_at (Act.static p) le_rfl
-- standard unit formal parameter
def headway : S:= someJ id
lemma Act.headway(n:ℕ):Act n id headway:=⟨contDiffAt_id,fun _ _=>rfl⟩
lemma head_light : light headway:= by simp [light,headway]
lemma ren_head (p:Word V): ren headway p=p:= funext fun i=> let H:=Act.swell p (show i ≤ i from le_rfl); ((Act.headway i).dial H head_light).trans_at H le_rfl
lemma head_ren (h:light x): ren x headway=x:= funext fun i=> let H:=Act.swell x (show i ≤ i from le_rfl);(H.dial (Act.headway _) h).trans_at H le_rfl
lemma tip_head : headway 1=1:=by unfold headway; rw [voyage]; exact (hasDerivAt_id 0).deriv
end
end YM.PositionX.Jet
