import YM.RGComparison.Core16.Silk.Parcel
/-!
# Visible packet covariance localization from wires

Product realized as actual evaluator before representing in common word algebra ∑ powers. PCB preserves full
 Φ in conditional Wick. This consumes arbitrary finite point columns only and DOES NOT replace any momentum
 plane aperture or winding bill post readout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Push.Uniform Precision Finset
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius

section series
-- pay truncation interaction of composing Series. Pinned factorial (internal unmarked) not double counting when applying bilinear pair covariance.
variable {V W : ℕ→Roll}
def morning (V:ℕ→ Roll)(W:ℕ→Roll)(i:ℕ):Roll:= ∑ q∈antidiagonal i,V q.1* W q.2
lemma subday : day (morning V W) 0 = day V 0 * day W 0 := by
    ext n
    let D:=range (n+1); let P(q:ℕ×ℕ):=V q.1 * W q.2; let L(i:ℕ)(q:ℕ×ℕ):=nth n (shiftFront i (P q))
    have he :nth n (day (morning V W) 0)= ∑ i∈D,∑ q∈antidiagonal i,L i q:=by
        unfold L; simp only [nth,dawn,day,morning,PowerSeries.coeff_mk,shiftFront,Nat.zero_add,Finset.mul_sum,map_sum]; rfl
    have hv: nth n (day V 0*day W 0)=nth n (dawn V 0 n*dawn W 0 n):=by
        simp only [nth,PowerSeries.coeff_mul]; refine sum_congr rfl (fun k hk=>?_); have hk:= mem_antidiagonal.mp hk; exact congr_arg₂ (·*·) (vogue (show k.1≤0+n by omega)) (vogue (show k.2≤0+n by omega))
    have hx : nth n (dawn V 0 n*dawn W 0 n)= ∑ q∈D×ˢ D,L (q.1+q.2) q:=by
        unfold L nth dawn; simp_rw [Finset.sum_mul,Finset.mul_sum,map_sum,Nat.zero_add]; rw [Finset.sum_product]; apply sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => congr_arg (nth n) ?_)); unfold shiftFront; change _=PowerSeries.X^(i+k)*(V i*W k); rw [pow_add]; ring
    have hI: (D.biUnion antidiagonal) ⊆ D ×ˢ D:=by
        intro i hi; obtain ⟨j,hj,h'⟩:=Finset.mem_biUnion.mp hi; have h:=Finset.mem_antidiagonal.mp h'; have h₁ := mem_range.mp hj; exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
    change nth n _ =nth n _; rw [he,hv,hx]; calc ∑ i∈D,∑ q∈antidiagonal i,L i q
                          _ = ∑ i∈D,∑ q∈antidiagonal i,L (q.1+q.2) q := sum_congr rfl fun i _=>sum_congr rfl fun j hj=> (mem_antidiagonal.mp hj) ▸ rfl
                          _ = _ := ?_
    rw [←Finset.sum_biUnion (f:=fun i=> L (i.1+i.2) i)]; swap; exact fun i a j a' h=>Finset.disjoint_left.mpr (fun z hi hj=> h ((mem_antidiagonal.mp hi).symm.trans (mem_antidiagonal.mp hj)))
    refine sum_subset hI (fun j _ hj=>?_); unfold L nth shiftFront; rw [PowerSeries.coeff_X_pow_mul',if_neg (show ¬j.1+j.2≤n from (fun h'=> hj (mem_biUnion.mpr ⟨j.1+j.2,mem_range.mpr (by omega),mem_antidiagonal.mpr rfl⟩)))]
end series

variable {G:Gauge}{S:Side}{ι k T A D L I: Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D][Fintype L][Fintype I]
variable {X:Shelf G A D} {P:Planet X S ι k T} {Q:ℕ→ℕ→ℝ} {o:ι→ℕ}
variable (p:Stuff G ι L)(q:Stuff G ι I)(ψ:(L→ G.Color)→ℝ)(φ:(I→G.Color)→ℝ)

def woven (p:Stuff G ι L)(q:Stuff G ι I) : Stuff G ι (L⊕I):= Sum.elim p q

def unite (ψ:(L→G.Color)→ℝ)(φ:(I→G.Color)→ℝ) (u:L⊕I→ G.Color):= ψ (u ∘ Sum.inl)*φ (u ∘ Sum.inr)

omit [Fintype ι] [Fintype L] [Fintype I] in
lemma coveredBy [DecidableEq ι] {Z W:Finset ι}{x:ℝ} (h:celery p Z x)(hv:celery q W x):celery (woven p q) (Z∪W) x:=by
   intro i; cases i with
   | inl i=> specialize h i; change Sum.elim _ _ (p i); rcases he:p i with _|_ <;> rw [he] at h; apply mem_union_left _ h; exact h
   | inr i=> specialize hv i; change Sum.elim _ _ (q i); rcases he:q i with _|_ <;> rw [he] at hv; apply mem_union_right _ hv; exact hv

variable {p q ψ φ} (hψ:ContDiffAt ℝ ω ψ 0)(hφ:ContDiffAt ℝ ω φ 0)
include hψ hφ

lemma mixed_hot : ContDiffAt ℝ ω (unite ψ φ) 0:= by
    let u(p:L⊕I→ G.Color):=(p∘Sum.inl); let v(p:L⊕I→G.Color):=(p∘Sum.inr)
    exact (hψ.comp (f:=u) _ (contDiff_pi.mpr (fun i=> contDiff_apply ℝ G.Color (Sum.inl i:L⊕I)) |>.contDiffAt)).mul (hφ.comp (f:=v) _ (contDiff_pi.mpr (fun i=> contDiff_apply ℝ G.Color (Sum.inr i:L⊕I))|>.contDiffAt)) -- index and comp norm?

omit [Fintype ι] in
lemma tuple (n:ℕ)(g:ℝ) (x:Sky G ι): tale (woven p q) (unite ψ φ) n g x=∑ j∈antidiagonal n,tale p ψ j.1 g x*tale q φ j.2 g x:=by
    let y:=book p g x; let z:=book q g x; let u:= book (woven p q) g x; let F (a:ℝ):=unite ψ φ (a • u)
    exact congr_fun (Aspiration.unique (directions ((mixed_hot hψ hφ).of_le le_top) u) (Aspiration.prod (directions (hψ.of_le le_top) y) (directions (hφ.of_le le_top) z))) n|>.trans (by unfold Tested.conv term; rw [PowerSeries.coeff_mul]; simp only [PowerSeries.coeff_mk]; rfl)

-- J roles: left-ordered standard `(L first, I second)` so price.nth_Silk.gap expects `I` then `L`? gap P w u = price P (u++w)-... so use gap P w=weave q, u=weave p; nest (k,i) accordingly.
variable (P)
def twin (p:Stuff G ι L)(q:Stuff G ι I)(ψ:(L→G.Color)→ℝ)(φ:(I→G.Color)→ℝ) (C : Rail G ι→ Rail G ι→Roll) (i j:ℕ):=night q φ (fun w=> night p ψ (C w) [] i) [] j

def joins (p:Stuff G ι L)(q:Stuff G ι I)(ψ:(L→G.Color)→ℝ)(φ:(I→G.Color)→ℝ)(r:ℕ):= twin p q ψ φ (fun w u=>price P (u++w)) r
omit hψ hφ [Fintype ι] in
lemma tale_streak (p:Stuff G ι L) (ψ:(L→G.Color)→ℝ)(g:ℝ)(i:ℕ) : Continuous (tale p ψ i g):=by
    rw [show tale p ψ i g=_ from funext (tracing p ψ i g)]; exact continuous_finsetSum _ fun i _=>continuous_const.mul (sing_cont ..)
lemma join_bill (H:P.Steady)(i:ℕ): night (woven p q) (unite ψ φ) (price P) [] i=∑ j∈antidiagonal i, joins P p q ψ φ j.1 j.2:= by
    let m g(a : ℕ)(b:ℕ):=tale p ψ a g*tale q φ b g; let funF j k g:=P.expect g (m g j k)
    let I:=antidiagonal i
    have he (j k):train (funF j k) (joins P p q ψ φ j k):= by
       let Q (a:Wires G _ k) (x:Wires G L j):= price P (weave p x++weave q a); let f (x:Wires G L j) := tagPrice p ψ x; let g (a: Wires G _ k):= tagPrice q φ a; let V y (a:Wires G _ k) (x: Wires G _ j):= sing (weave p x ++ weave q a) y
       let u (a: Wires G _ k)(x: Wires G _ j) y:= P.expect y (V y a x)
       rw [show joins P p q ψ φ j k= ∑ a,g a • ∑ x,f x • Q (a: Wires G _ k) x from by unfold joins twin night; simp only [List.append_nil]; rfl]
       refine (train.join (fun a=> g a • ∑ x,f x • u a x) _ univ (fun a _=> train.lift (train.join (fun x=> f x • u a x) _ univ (fun x _ => (supplies (weave p x++ weave q a) H).lift (f x))) (g a))).travel ?_
       filter_upwards [Fk.tollLess (willing H.prices)] with y hy
       let F (a: Wires G _ k):= ∑ x,f x • V y a x; have hF a (x: Wires G _ j): Continuous (f x • V y a x):= continuous_const (y:=f x)|>.smul (sing_cont ..)
       rw [show funF j k y=P.expect y (∑ a,g a • F a) from ?_,Planet.paid H hy _ (fun a=>g a • F a) (fun a _=>?_)]
       · simp_rw [Finset.sum_apply,Pi.smul_apply,Planet.expect_mul,smul_eq_mul]; refine sum_congr rfl (fun i _=>?_); unfold F; rw [Planet.paid H hy _ (fun x=> f x • V y i x) (fun x _=> havenreal (hF i x))]; simp only [Planet.expect_mul]; rw [Finset.sum_apply]; rfl
       · apply havenreal; exact continuous_const (y:=g a)|>.smul (by have h:F a= fun y=> ∑ x,(f x • V _ a x) y:= funext (fun i=> Finset.sum_apply ..); rw [h]; exact continuous_finsetSum _ fun i _=> hF a i) -- ambiguity
       unfold funF m; congr 1; ext x; simp_rw [Finset.sum_apply,Pi.smul_apply,Pi.mul_apply,F,Finset.sum_apply,Pi.smul_apply,smul_eq_mul, Silk.tracing,V,sing_join]; rw [mul_comm (_:ℝ),sum_mul]; apply sum_congr rfl; intro a _; simp_rw [mul_sum]; refine sum_congr rfl (fun i _=>?_); unfold f g; ring
    apply (solder P (woven p q) _ H [] i).unique; refine (train.join (fun j:ℕ×ℕ=>funF j.1 j.2) _ I (fun a _=>he a.1 a.2)).travel ?_
    filter_upwards [Fk.tollLess (willing H.prices)] with x hx; unfold sight; rw [show sing (ι:=ι) (G:=G) [] x=1 from rfl,one_mul]
    have hu:tale (woven p q) (unite ψ φ) i x=∑ j∈I,m x j.1 j.2:= by funext a; rw [Finset.sum_apply]; apply tuple hψ hφ
    rw [hu,Planet.paid H hx I _ (fun j hj=> ?_),Finset.sum_apply]
    apply havenreal; apply Continuous.mul (tale_streak ..) (tale_streak ..) -- inspect. easier charge via story from hP templates? not Have celery. book continuous

end YM.RGComparison.Core16.Silk
