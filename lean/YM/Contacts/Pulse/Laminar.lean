import YM.Contacts.Pulse.Stitch
import YM.Extra.ITERATION_NO_LOSS.Sums
/-! Differing spaces/row/column budgets. No need to turn coercions into
extra traced legs. Column factor paid *once* for the full substitution. -/
noncomputable section
namespace YM.Pulse
open Function Set Finset Filter RG Push.AbsoluteSums Extra.Iteration
open scoped Classical Topology BigOperators NNReal
variable {ι κ X Y Z α β : Type*}


structure Ripple (l:Range X)(m:Range Y)(t:X→ Y→ℝ) : Prop where
  one x y : 1≤t x y
  span x y u v : m.step u v≤ t x u*l.step x y*t y v
structure Weirs (t : X→Y→ℝ)(G:X→Y→ℝ)(a b:ℝ) : Prop where
  left : 0 ≤ a
  right : 0 ≤ b
  columns y : SumBudget (fun x=> ‖G x y‖ * t x y) a
  rows x : SumBudget (fun y=> ‖G x y‖ * t x y) b
lemma Range.echo (l:Range X): Ripple l l l.step := ⟨fun _ _=> l.one_fee, fun x y u v=> by
  apply (l.triangle _ y _).trans; gcongr; have h:= l.triangle u x y; unfold Range.step at *; rw [l.mirror u x] at h; exact h⟩
lemma Track.flow {l:Range X}{G a} (h:Track l G a): Weirs l.step G a a:= ⟨h.cash,h.cash,h.col,h.row⟩

variable [Fintype ι]
lemma budget_pi {f:ι→X→ℝ}{a:ι→ℝ}(h:∀ i, SumBudget (f i) (a i)): SumBudget (fun p:ι→X=>∏ i, f i (p i)) (∏ i, a i) := by
  let e:= (Fintype.equivFin ι).symm; have he (p:ι→ℝ) : (∏ i,p i)=∏ i,p (e i):= (Equiv.prod_comp e p).symm
  simp_rw [he (p:=a)]; refine budget_map (Cost.pi (fun i=> h (e i))) (fun p:ι→X=>p ∘ e) (fun x y h=> ?_) (fun p=>he _)
  exact funext (e.surjective.forall.mpr fun i=> congr_fun h i)

lemma budget_locked_prod {f:ι→ X→ℝ}{a:ι→ℝ}(i:ι) (h: ∀ j ∈ (univ.erase i), SumBudget (f j) (a j)) (x:X) : SumBudget (fun p:Locked X i x=> ∏ j∈(univ.erase i), f j (p.val j)) (∏ j∈(univ.erase i), a j):= by
  let β:= univ.erase i; have he (p:ι→ℝ) : (∏ j∈β,p j)=∏ j:β,p (j:ι):= (Finset.prod_attach ..).symm
  simp_rw [show univ.erase i=β from rfl, he a]
  refine budget_map (budget_pi (ι:=↥β) (fun j=> h _ j.property)) (fun p:Locked X i x=> p.val ∘ (Subtype.val : ↥β→ι)) (fun p q h=> Subtype.ext ?_) (fun p=> he _)
  funext j; by_cases hj : j=i
  · subst j; rw [p.property,q.property]
  exact congr_fun h (show ↥β from ⟨j, Finset.mem_erase.mpr ⟨hj,mem_univ _⟩⟩)

variable {l : Range X} {m:Range Y} {F : Field ι X} {t:X→Y→ℝ}
def allAt (G:ι→ X→Y→ℝ)(F:Field ι X) (y:ι→Y) := ∑' x:ι→X,F x * ∏ i:ι,G i (x i) (y i)
variable {G:ι→ X→Y→ℝ} {a b:ι→ℝ}{c d:ℝ}
lemma Ripple.cost (z:Ripple l m t)(x:ι→X)(y:ι→Y): m.bill y ≤ l.bill x * ∏ i:ι,t (x i) (y i):= by
  let f i:= t (x i) (y i); have hu i:1 ≤ f i:= z.one ..
  have he:1 ≤ ∏ i,f i:= one_le_prod fun i _=>hu _; have hx:=l.one_bill x
  refine m.wide _ (one_le_mul_of_one_le_of_one_le hx he) ?_
  intro i j; by_cases h:i=j; · subst j; simp only [Range.step,m.flat]; exact one_le_mul_of_one_le_of_one_le hx he
  calc
    m.step _ _ ≤ f i*l.step (x i) (x j)* f j:= z.span ..
    _ ≤ f i*l.bill x* f j := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (l.width x i j) (zero_le_one.trans (hu _))) (zero_le_one.trans (hu _))
    _ = l.bill x*(∏ k∈ ({i,j}:Finset ι),f k):= by rw [prod_insert (by simpa using h),Finset.prod_singleton]; ring
    _ ≤ _:= mul_le_mul_of_nonneg_left (prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun i _=>zero_le_one.trans (hu _)) fun i _ _=> hu _) (by positivity)

lemma laminar (h : Rooted l F c)(hc:Ripple l m t)(hx:∀ i,Weirs t (G i) (a i) (b i))(i:ι)(y:Y): SumBudget (fun p:Locked Y i y×(ι→X)=> ‖F p.2 * ∏ j, G j (p.2 j) (p.1.val j)‖*m.bill p.1.val) ((a i*c)*(∏ j ∈ univ.erase i,b j)):= by
  let g j x y:= ‖G j x y‖* t x y
  have hh j x y : 0 ≤ g j x y:= (hx j).columns y|>.1 x
  let u (x:ι→X):= ‖F x‖ * l.bill x
  have hu x:0 ≤ u x:= by unfold u; positivity
  let f (p:(z:X)×Locked X i z):= g i p.1 y * u p.2.val; let B:= ∏ j ∈ univ.erase i, b j
  have hF : SumBudget f (a i*c):= by
    refine sigma_total _ _ (fun z=> budget_scale (hh i z y) (h.row i z)) ?_
    simpa only [g,mul_comm c] using Cost.scale' ((hx i).columns y) c h.cash
  let P:= fun x : (p:(z:X)×Locked X i z)×Locked Y i y=> f x.1 * (∏ j∈ univ.erase i,g j (x.1.snd.val j) (x.2.val j)); -- sigma
  have hB : 0≤B:= prod_nonneg fun j _=> (hx j).right
  have hP : SumBudget P ((a i*c)*B):= by
    refine sigma_total _ _ (fun x=> budget_scale (hF.1 x) (budget_locked_prod (f:=fun j y=>g j (x.snd.val j) y) i (fun j _=> (hx j).rows (x.2.val j)) y)) ?_
    exact Cost.scale' hF B hB
  let V (p:Locked Y i y× (ι→X)): (p:(z:X)×Locked X i z)×Locked Y i y:= ⟨⟨p.2 i, p.2, rfl⟩,p.1⟩
  have hv : Injective V:= fun p q h=> Prod.ext (congr_arg (fun x=>x.2) h) (congr_arg (fun x=>x.fst.snd.val) h)
  apply budget_mono (budget_pull _ hv hP) (fun _=> by positivity); rintro ⟨q,x⟩
  simp only [norm_mul,norm_prod]; apply le_trans (mul_le_mul_of_nonneg_left (hc.cost x q.val) (by positivity)); apply le_of_eq
  rw [mul_mul_mul_comm,←prod_mul_distrib]; dsimp only [P,V,f,u]; rw [← show g i (x i) (q.val i)=_ from congr_arg (g i (x i)) q.property]
  rw [← Finset.mul_prod_erase univ (fun j=>‖G j (x j) (q.val j)‖* t (x j) (q.val j)) (mem_univ i)]
  unfold g; ring
lemma all_root (h : Rooted l F c)(hc:Ripple l m t)(hx:∀ i,Weirs t (G i) (a i) (b i))(H:∀ i,(a i*c)*(∏ j ∈ univ.erase i,b j)≤ d) (hd:0≤ d): Rooted m (allAt G F) d:=
  ⟨hd,fun i x=> budget_loosen (budget_join (v:=fun x:Locked Y i x=>m.bill x.val) (fun _=>by positivity) (laminar h hc hx i x)) (H i)⟩
lemma all_summable [Nonempty ι] (h : Rooted l F c)(hc:Ripple l m t)(hx:∀ i,Weirs t (G i) (a i) (b i))(y:ι→Y) : Summable (fun x:ι→X=> ‖F x* ∏ i, G i (x i) (y i)‖) := by
  inhabit ι; exact (summable_mul_right_iff (zero_lt_one.trans_le (m.one_bill y)).ne').1 ((laminar h hc hx default (y default)).2.1.prod_factor ⟨y,rfl⟩)
end YM.Pulse
