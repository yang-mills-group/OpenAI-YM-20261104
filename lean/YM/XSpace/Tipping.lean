import YM.XSpace.Purlet

/-!
# Relative Wick gauge: Carrier density using both the tree and an alternate covariant meeting

A fixed-order gauge-fixing comparison (does not claim higher-order valid with alternate
Jacobian 1; needs actual Jacobian higher terms in applying such comparison at higher orders).
`Reading` costs later may be proved with covGauge at order one.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open Function Module JetGauge Contraction Source Source.Drops Labels Lattice RG Wilson Next.Rank.Normal
open Finsupp PowerSeries
open scoped Topology BigOperators InnerProductSpace
variable {G:Gauge} {R:Period} (T:R.Tree)

def snack (G : Gauge) : Knobs T G → T.Key G →₀ℂ:= Sum.elim (fun i=> single i 1) (fun _=> 0)
def thin (G:Gauge):= Next.Rank.Normal.scope (snack T G) (Bare.Q T G)
lemma term_snack (i j:T.Key G): (thin T G).cov (.inl i) (.inl j)= ↑(T.covariance G i j):=by unfold thin; dsimp only [scope,snack,Sum.elim_inl]; rw [treats_single]; simp; rfl
lemma term_empty (G:Gauge) (j) (i): (thin T G).cov (.inr i) j=0:=by change treats _ 0 _=_; simp [treats,linearCombination_apply]
lemma kept_block (i j:T.Key G): (guiding T G).k.cov (.inl i) (.inl j)= ↑(T.hessian G i j):=by simp only [guiding,spaceCharge,axisB_hor,Period.Tree.hessian, LinearMap.BilinForm.toMatrix_apply]; rfl
lemma term_fit (G:Gauge): (guiding T G).Fit (thin T G):=by
  have h (i j:T.Key G): (∑ k:T.Key G, (T.hessian G i k)*(T.covariance G k j))=if i=j then 1 else 0:= (congr_fun (congr_fun (T.covariance_val G) i) j).trans (Matrix.one_apply ..)
  refine ⟨?_,?_⟩
  · rintro (i|i) (j|j) h; rw [term_snack,cov_chosen T G i j h]; simp
    rw [(thin T G).symm]; exact term_empty ..; exact term_empty ..; exact term_empty ..
  rintro (i|i) (j|j) hj
  · rw [Fintype.sum_sum_type]
    simp_rw [kept_block,term_snack]; rw [show ∑ k, (guiding T G).k.cov (.inl i) (.inr k)*(thin T G).cov (.inr k) (.inl j)= 0 from Finset.sum_eq_zero fun k _=> by rw [term_empty,mul_zero], add_zero]; simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum, h]
    split; subst j; simp [Legs.chosen_eq]; next e=> rw [Legs.chosen_ne (by intro h; injection h with h; exact e h.symm)]; simp
  · exact False.elim (outside T _ hj)
  · rw [Finset.sum_eq_zero,Legs.chosen_ne (by simp)]; intro k _; rw [(guiding T G).radical _ (outside T i),zero_mul]
  exact False.elim (outside T _ hj)
lemma munch (p : poly (Knobs T G)) (A:T.Field G): Taylor.evalAt (T.basis G) A (exchange (snack T G) p)=readAt T (A,0) p:= by
  rw [Taylor.evalAt, reads_val]; unfold readAt Taylor.evalAt; congr 2; funext i; cases i <;> simp [reads,snack,axisB]
lemma thread_thin (G:Gauge) (P:St (Per R.side) G): E (thin T G) (Lift T P)= E (treeCov T G) P:=by
  rw [← transfers, E,thin, ← show reads (snack T G) (0:T.Key G→ℂ) = 0 by ext i; simp [reads], ← wets]; congr 1; apply Taylor.from_real (T.basis G); intro x; rw [munch,woven_at,log_path,from_hor]

-- meeting condition on a whole periodic covariance

def pressure (R:Period) (G:Gauge) : LinearMap.BilinForm ℝ (R.Bonds→ G.Color):= (1/2:ℝ) • ∑ p:Face (Per R.side), (innerₗ G.Color).compl₁₂ (linearFace p) (linearFace p)
lemma press (A B:R.Bonds→G.Color): pressure R G A B=(∑ p:Face (Per R.side), inner ℝ (linearFace p A) (linearFace p B))/2:=by unfold pressure; simp only [LinearMap.sum_apply,LinearMap.smul_apply]; rw [div_eq_inv_mul]; norm_num; ring
lemma bill (A B:Carrier T G): spaceCharge T G A B= pressure R G (route T A) (route T B):=by rw [press,spacelike]
structure Meet (G:Gauge) (R:Period) where
  index : RealDual (G:=G) (R:=R) →ₗ[ℝ] (R.Bonds → G.Color)
  mono (c:G.ColorIndex) (v): index (v ∘ₗ light c)=light c (index v)
  symm (v w:RealDual (R:=R) (G:=G)): v (index w)=w (index v)
  leg (v): Legit R (index v)
  eligible (A:R.Bonds→G.Color): Legit R A → R.curl (index (pressure R G A))= R.curl A
variable (M:Meet G R)
def wide : JetGauge.Cov (Roller R G) :=⟨fun i j=> ↑(reading i (M.index (reading j))), fun i j=> by rw [M.symm]⟩
def roots (i:Knobs T G): RealDual (R:=R) (G:=G):=(axisB T G).coord i ∘ₗ park T
def moving : JetGauge.Cov (Knobs T G) := ⟨fun i j=> ↑(roots T i (M.index (roots T j))),fun i j=> by rw [M.symm]⟩
lemma spilled (v:Module.Dual ℝ (Carrier T G)) (A:R.Bonds→G.Color):
    v (park T A)=∑ i:Knobs T G,roots T i A * v (axisB T G i):=by
  conv_lhs=>rw [← (axisB T G).sum_repr (park T A),map_sum]; simp only [map_smul]
  rfl
lemma roots_degree (c:G.ColorIndex) (i:Knobs T G) : roots T i ∘ₗ light c=if key T i=c then roots T i else 0:=by
  split_ifs with he <;> apply LinearMap.ext <;> intro x <;> change (axisB T G).repr (park T (light c x)) i = _ <;> rw [color_park,key_pixel] <;> simp only [he,↓reduceIte] <;> rfl
lemma monochrome (i j:Knobs T G) (h:key T i≠key T j): (moving T M).cov i j=0:=by
  have he : M.index (roots T i)=light (key T i) (M.index (roots T i)):= by nth_rw 1 [← show roots T i ∘ₗ light (key T i)=roots T i by rw [roots_degree, if_pos rfl]]; exact M.mono ..
  change ((roots T i (M.index (roots T j)):ℝ):ℂ)=0; rw [M.symm,he, ← LinearMap.comp_apply, roots_degree,if_neg (Ne.symm h),LinearMap.zero_apply,Complex.ofReal_zero]

lemma price_inverse (G : Gauge) (R : Period) (M:Meet G R) (T:R.Tree) (x:Carrier T G) (j:T.Key G): (∑ s:Knobs T G, (spaceCharge T G x (axisB T G s) * roots T s (M.index (roots T (.inl j)))))= (axisB T G).repr x (.inl j):=by
  set p:=roots T (.inl j)
  let A:= M.index (pressure R G (route T x))
  have he (v): route T (park T (M.index v))= M.index v:= by rw [undo_park,polar_keeps _ (M.leg _)]
  have hp : (park T A).1=x.1:= by
    apply T.curl_injective; change R.curl _= _; rw [← route_curl T (park T A),he, M.eligible _ (legit_route T _), route_curl]; rfl
  have h : p A=(axisB T G).repr x (.inl j):= by change (axisB T G).repr (park T A) (Sum.inl j)=_; rw [axisB,Basis.prod_repr_inl,Basis.prod_repr_inl,hp]
  rw [← h,show p A=_ from M.symm p (pressure R G (route T x)), ← he p, ← bill,spilled, he]; exact Finset.sum_congr rfl fun _ _=> mul_comm ..
lemma moving_fit : (guiding T G).Fit (moving T M):= by
  refine ⟨monochrome T M,?_⟩
  rintro i (j|j) hj; change (∑ k:Knobs T G, ((spaceCharge T G (axisB T G i) (axisB T G k):ℝ):ℂ)*↑(roots T k (M.index (roots T (.inl j)))))=_
  simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_sum, price_inverse G R M T (axisB T G i),Basis.repr_self]; by_cases h : i=.inl j; simp [h, Legs.chosen_eq]
  rw [Legs.chosen_ne (Ne.symm h), Finsupp.single_eq_of_ne (Ne.symm h), Complex.ofReal_zero]
  exact False.elim (outside T _ hj)
lemma wide_carry (p : RealDual (R:=R) (G:=G)) (z) : p (M.index z)=∑ i, roots T i (M.index z) * p (route T (axisB T G i)):=by
  have ht:= spilled T (p.comp (route T)) (M.index z); simp only [LinearMap.comp_apply,undo_park, polar_keeps _ (M.leg z)] at ht; exact ht
lemma scope_woven : wide M= scope (woven T) (moving T M):=by
  apply Next.Rank.Normal.Symmetric.ext; funext i j; change ↑(reading i (M.index (reading j)))= treats _ _ _; rw [woven,woven,treats_sum,wide_carry T M, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun s _=>?_ ; rw [treats_comm,treats_sum]; push_cast; rw [M.symm,wide_carry T M,Complex.ofReal_sum,Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; rw [treats_single]; push_cast; simp only [moving]; ring
lemma into_wide (P:St (Per R.side) G): E (moving T M) (Lift T P)= E (wide M) P:=by rw [Lift,E,wets,← scope_woven]; rw [show reads (woven T (G:=G)) 0=0 from funext fun i=>by simp [reads]]
lemma setting {A:PowerSeries (St (Per R.side) G)} (h:Good (R:=R) A): E (wide M) (price1 (R:=R) A) = E (treeCov T G) (price1 (R:=R) A):= by rw [← into_wide T, ← thread_thin T]; exact JetGauge.Setup.invariant _ _ (ambient T A h) _ _ (moving_fit T M) (term_fit T G)
lemma order1_always {Z : Type*} {q:Z→ℕ} {H:Hol G} (v:∀ i:Z,Survey G H (q i)) (k:∀ i:Z, Labels.Label G (q i)) (a: Z→ R.Sites) (s: Finset Z):
    let X:=∏ i∈s,toy (v i) (a i) ((v i).insertW (-1) (k i)).val
    coeff 1 (Bare.normalized T G (∏ i∈s, Bare.column T (v i) (a i) (k i)))=blend (wide M) 0 (price1 (R:=R) X):=by dsimp only; rw [reconstruct1]; exact (setting T M (good_list (R:=R) s (fun i=> toy (v i) (a i) _) (fun i _=> good_toy (v i) (a i) ((v i).insertW (-1) (k i))))).symm
end YM.XSpace.Chart2
