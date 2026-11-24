import YM.QuadraticLocal.Germ.Obey
import YM.Next.SCHEDULE.TensorCost
/-!
 ## Multilinear landings, on the exact inputs
 Need coherence across tests after any kinetic-coupling comparison with the
 REAL numerical kernels (many are germ-level analytic rather than an identity
 on whole determinant). Use frame issuer of Stash; keep complete norms & assessments
 on the *boundary* as well as interior stencils. Here part I handles why pure queries
 on a Budget can recover germ-valued typed kernels and addresses. A strengthening for
 genuinely controlled analyticity off the I/O hull (e.g. positivity behind flags) would
 require extra and isn't used for these paths.
 No cut-off mask derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tint
open Function Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
namespace Pure
variable {T X : Type*} {u w d:ℝ} {c: Side} {G:Gauge}
variable (f g : T→ℝ)

/-- Even zero paint supported in the SAME stencil rows. -/
def Ray := ∃ a:ℝ,g=fun i=> a*f i
variable {f g} {h:T→ℝ}
lemma dawn : Ray f (fun _=>0) := ⟨0,funext fun _=>by simp⟩
lemma hue (a:ℝ) : Ray f fun x=> a*f x:= ⟨a,rfl⟩
lemma idles (hg:Ray f g)(hh:f=0): g=fun _=>0 := by obtain ⟨i,rfl⟩:= hg; rw [hh]; simp
lemma stock (hg:Ray f g)(hq:Ray f h): Ray f (fun i=> g i+h i):= by obtain ⟨x,rfl⟩:=hg; obtain ⟨y,rfl⟩:=hq; exact ⟨x+y,funext fun i=> (add_mul ..).symm⟩
lemma verse (u:ℝ) (hg:Ray f g): Ray f (fun x=>u*g x):=by obtain ⟨i,rfl⟩:=hg; exact ⟨u*i,funext fun x=> (mul_assoc ..).symm⟩
lemma smith {f' : T→ℝ}(hg:Ray f g)(hp:Ray h f'): Ray (fun x=> f x*h x) (fun x=> g x*f' x):=by
    obtain ⟨c,rfl⟩:=hg; obtain ⟨v,rfl⟩:=hp; exact ⟨c*v,funext fun x=> (by dsimp only; ring)⟩
lemma script {α:Type*}(S:Finset α) (p:α→T→ℝ) (hp:∀ i∈S, Ray f (p i)): Ray f fun t=> ∑ i∈S, p i t:=by
    induction S using Finset.induction with
    | empty=> simp_rw [Finset.sum_empty]; exact dawn
    | insert i s hi IH=> simp_rw [Finset.sum_insert hi]; exact stock (hp i (mem_insert_self ..)) (IH fun i hi=> hp i (mem_insert_of_mem hi))
lemma still [MeasurableSpace X] (μ:Measure X) (φ:X→T→ℝ)(hp:∀ x,Ray f (φ x)) : Ray f (fun i=> ∫ x,φ x i ∂μ):=by
    choose c hc using fun x=>hp x; refine ⟨∫ x,c x ∂μ, funext fun i=>?_⟩; change (∫ x,φ x i ∂μ)=_; simp_rw [hc]; exact MeasureTheory.integral_mul_const _ _

open RemainderComparison Collar
variable {ι:Type}
variable (S:Set ι)(Q:ι→T→ℝ)
set_option quotPrecheck false
local notation "Πs" R:max t:max=> ((Multiset.map (fun i=> Q i t) R).prod)
def lesson : Lesson ι T where
    Knows q f:= (∀ x∈ q,x∈ S) → Ray (fun t=>Πs q t) f
    pitch _ hg h:= Pure.verse _ (hg h)
    choir hf hg h:= stock (hf h) (hg h)
    nil _ _:= dawn
    constant a h:= by change Ray _ _; refine ⟨a,?_⟩; simp
    shares := by
       intro p q f g hf hg h
       simp_rw [Multiset.map_add,Multiset.prod_add]; apply smith (hf (fun k hk=> h k (Multiset.mem_add.mpr (Or.inl hk)))) (hg (fun k hk=> h k (Multiset.mem_add.mpr (Or.inr hk))))
    meal h _ hg:=still _ _ (fun i=>h i hg)
-- reader scaling if analytical ticket outputs from REAL Pocket, ANY such factor slope for frame future.
lemma selected {α:Type*}(f:α→ℝ) (h:∀ i:α,‖f i‖≤u)(hp:f≠0): ∃ i:α, f i≠0 ∧ ∀ j,|f j|≤ 2*|f i| :=by
   let V:Set ℝ:=Set.range (fun i=> |f i|); have he:BddAbove V:= ⟨u,fun z hz=>by obtain ⟨j,rfl⟩:=hz; exact h j⟩
   obtain ⟨i,hi⟩:= Function.ne_iff.mp hp; have hv:sSup V>0:= lt_of_lt_of_le (abs_pos.mpr hi) (le_csSup he (show |f i|∈ V from ⟨_,rfl⟩)); have hz:V.Nonempty:= ⟨_,i,rfl⟩; obtain ⟨b,hb,h'b⟩:= exists_lt_of_lt_csSup hz (half_lt_self hv); obtain ⟨v,rfl⟩:=hb; refine ⟨v,abs_pos.mp ((half_pos hv).trans h'b), fun j=>?_⟩; exact (le_csSup he (show |f j| ∈ V from ⟨_,rfl⟩)).trans (by linarith)
variable (P:BudgetPoint) (A:Support c) (f F:T→ℝ)(X:T→ Config G c→ℝ) (v:Config G c→ℝ)
-- Use with X=y pure-dependent and p(t). painting *Budget*; no occurrence of disjoint Authority keys repeated.
local notation "Y" x:max=> Healthy P.threshold A x
structure Coherent (P:BudgetPoint)(A:Support c)(f:T→ℝ) (q:ℝ) (g:T→ Config G c→ℝ):Prop where
   stage : ∃ G0:Config G c→ℝ, P.Regular A G0∧∀ t:T,g t=f t • G0
   light : ∀ t:T, ∀ x∈A, P.supBounds x A (g t) q
lemma coherent (u:ℝ) (hq:∀ i,‖f i‖≤u)(U0:ℝ) (hd:0≤d) (hp:∀ x:Config G c,Y x→Ray f (fun i=>X i x))
    (hP:∀ t,∃ z:Config G c→ℝ, P.Regular A z ∧ (∀ i∈A,P.supBounds i A z d) ∧ (∀ x:Config G c,Y x→ X t x= (U0*f t)*v x+ z x)):
    ∃ Z:T→ Config G c→ℝ, Coherent P A f (2*d) Z ∧ (∀ t x,Healthy P.threshold A x→ X t x=(U0*f t)*v x + Z t x):= by
    by_cases hb:f=0;
    · refine ⟨fun _ _=>0,⟨⟨0,?_,fun t=>?_⟩,?_⟩,?_⟩;
      · exact AnalyticBridge.CouplingShape.reg_const 0
      · rw [hb]; simp; rfl
      · intro t x hx; refine AnalyticBridge.CouplingShape.sup_larger (AnalyticBridge.CouplingShape.sup_const (p:=P) (o:=x) (X:=A) (0:ℝ)) ?_; rw [abs_zero]; linarith
      intro t x hx; rw [show X t x=0 from congr_fun (Pure.idles (hp x hx) hb) t,hb]; simp
    obtain ⟨i,hi,hV⟩:= selected f hq hb; obtain ⟨z,hz,hZ,hK⟩:= hP i; let v' t:= (f t)/(f i); let Z t:= (v' t) • z; refine ⟨Z, ⟨ ⟨(f i)⁻¹ • z, AnalyticBridge.CouplingShape.reg_scale _ hz,fun t=>?_⟩,?_⟩ ,fun t x hx=>?_⟩
    · rw [smul_smul]; unfold Z v'; rw [div_eq_mul_inv]
    · intro t x hx; apply AnalyticBridge.CouplingShape.sup_larger (AnalyticBridge.CouplingShape.sup_scale _ (hZ x hx)) _; apply mul_le_mul_of_nonneg_right _ hd; unfold v'; rw [abs_div,div_le_iff₀ (abs_pos.mpr hi)]; exact hV t
    obtain ⟨Q,hQ⟩:= hp x hx; have he: X i x=Q*f i:=congr_fun hQ i; change X _ _ = _ + v' t * z x; rw [show X t x=Q*f t from congr_fun hQ t, show z x=Q*f i-U0*f i*v x from (by linarith only [he,hK x hx])]; unfold v'; field_simp; ring
end Pure
end YM.QuadraticLocal.Tint
