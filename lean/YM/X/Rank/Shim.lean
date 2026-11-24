import YM.X.Rank.Relate
/-!
# From preservation of correlations to a *single* orthogonal color identification

Used to test the matched positions before taking the tangent. Does not need
an assumption about real rank r three-tensor or connected Gauge group.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter MeasureTheory Matrix Maxwell Wick Maxwell.Free
open Screen Next.Rank.Normal MvPolynomial
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : ℕ} {r: WickPol G→WickPol G→ Prop}
structure Crew (r : WickPol G→ WickPol G→Prop) where
  p : WickPol G
  q : WickPol G
  joins : r p q
  clear : realForm p=p
  free : realForm q=q
  vector : Sample G

abbrev dataSet (x:Mat G)(u:WickPol G)(A:Sample G):ℝ := (helps (coatV x A) u).re
lemma data_val (x:Mat G)(u:WickPol G)(A:Sample G)(h:realForm u=u) : (↑(dataSet x u A):ℂ)=helps (coatV x A) u:= by
  refine Complex.ext rfl ?_; have he:= congr_arg Complex.im (helps_real (coatV x A) u); rw [h,Complex.star_def,Complex.conj_im] at he; rw [Complex.ofReal_im]; linarith only [he]

abbrev FamilyY (T : Crew r) (x:Tile G.ColorIndex):= dataSet (folio x) T.p T.vector
abbrev FamilyZ (T : Crew r) (x:Tile G.ColorIndex):= dataSet (folio x) T.q T.vector

variable {A:Type}(T:A→ Crew r)(hr: Rank.Relation r)(c:G.ColorIndex)
include hr c
lemma picture (P:MvPolynomial A ℝ)(f g:Tile G.ColorIndex→PTS A)(hf:f=fun x i=>FamilyY (T i) x)(hg:g=fun x i=>FamilyZ (T i) x): Mirrors (fun x=> ((↑(aeval (f x) P-aeval (g x) P):ℂ))) := by
  let f' (u:Tile G.ColorIndex)(p:MvPolynomial A ℝ):= ((aeval (f u) p:ℝ):ℂ); let g' (u:Tile G.ColorIndex)(p:MvPolynomial A ℝ):=((aeval (g u) p:ℝ):ℂ)
  let a (n:ℕ)(p: Fin n→A)(x:Tile G.ColorIndex):= ∏ i,f' x (X (p i))
  let b (n:ℕ)(p: Fin n→A)(x:Tile G.ColorIndex):= ∏ i,g' x (X (p i))
  have H n (p:Fin n→A) : Mirrors (fun x=>a n p x-b n p x):=by
      convert (Relation.mirrorWords c hr (q:=fun i=> (T (p i)).q) (p:=fun i=> (T (p i)).p) (fun i=> (T (p i)).joins) (fun i=>(T (p i)).vector)) using 1
      funext x; unfold a b f' g'; simp only [hf,hg,aeval_X,FamilyY,FamilyZ];simp_rw [fun z:Crew r => data_val (folio x) _ _ (Crew.clear z), fun z:Crew r => data_val (folio x) _ _ z.free]
  suffices he : ∀ n (q:Fin n→A), Mirrors (fun x=>a n q x*f' x P-b n q x*g' x P) by
    convert he 0 Fin.elim0 using 1; ext1 x; simp [a,b,f',g']
  induction P using MvPolynomial.induction_on with
  | C r => intro n q; convert (H n q).scales (↑r:ℂ) using 1; ext1 x; unfold f' g'; simp [smul_eq_mul,mul_sub]; ring
  | add p q hp hq => intro n v; convert (hp n v).plus (hq n v) using 1; ext1 x; simp only [f',g',Pi.add_apply,map_add,Complex.ofReal_add]; ring
  | mul_X p i hp=>
    intro n v; convert hp (n+1) (Fin.cons i v) using 1; ext1 x; simp only [a,b,f',g',map_mul, aeval_X, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul]; ring

omit c hr in
lemma gram_closed : IsCompact {x:Mat G| x.transpose*x=1} := by -- edit omit context
  let J:=G.ColorIndex; let f:= folio (J:=J) (V:=J)
  let K:={x:Tile J|Screen.gram x=1}; have he : IsClosed K:= isClosed_eq ((foli _).matrix_transpose.mul (foli _)) continuous_const
  have hK: IsCompact K:= by
    refine (isCompact_closedBall (0:Tile J) 1).of_isClosed_subset he ?_; intro i hi; refine mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun x=> ?_); rcases x with ⟨x,y⟩; have hk : Screen.gram i y y=1:= congr_fun (congr_fun hi y) y |>.trans (Matrix.one_apply_eq ..); unfold Screen.gram at hk; rw [Matrix.mul_apply] at hk
    have hv : (i (x,y))*(i (x,y)) ≤ 1:=by rw [← hk]; exact Finset.single_le_sum (f:=fun z=>i (z,y)*i (z,y)) (fun i _=>mul_self_nonneg _) (Finset.mem_univ x)
    rw [Real.norm_eq_abs]; nlinarith only [hv,sq_abs (i (x,y)),abs_nonneg (i (x,y))]
  rw [show {x:Mat G| _}= f '' K from (by
    ext x; constructor; intro hx; refine ⟨fun u: J×J=> x u.1 u.2,hx,rfl⟩; rintro ⟨y,h,rfl⟩; exact h)]
  exact hK.image (foli _)
lemma Relation.shim : ∃ X:Mat G,X.transpose*X=1∧ ∀ c:Crew r, dataSet X c.p c.vector=dataSet 1 c.q c.vector:= by
    let K:={X:Mat G| X.transpose*X=1}; let s (c:Crew r): Set (Mat G):= {x| dataSet x c.p c.vector=dataSet 1 c.q c.vector}; have hF c : IsClosed (s c) := isClosed_eq (Complex.continuous_re.comp (regularity c.vector c.p).continuous) continuous_const
    have h(s₀: Finset (Crew r)):∃ x∈ K,∀ i∈ s₀,x∈ s i:= by
       let a (x:Tile G.ColorIndex)(i : ↥s₀):=dataSet (folio x) i.val.p i.val.vector
       let b (x:Tile G.ColorIndex)(i : ↥s₀):=dataSet (folio x) i.val.q i.val.vector
       obtain ⟨x,hx,hq⟩:= Screen.detects a b (continuous_pi fun i=> Complex.continuous_re.comp ((regularity ..).continuous.comp (foli _))) (continuous_pi fun i=> Complex.continuous_re.comp ((regularity ..).continuous.comp (foli _))) (fun p=>picture (fun i:↥s₀=>i.val) hr c p a b rfl rfl)
       exact ⟨folio x, hx, fun i hi=>congr_fun hq ⟨i,hi⟩⟩
    obtain ⟨x,hK,hx⟩:= (gram_closed (G:=G)).inter_iInter_nonempty s hF (fun u=> by obtain ⟨x,hK,h⟩:=h u; exact ⟨x,hK,mem_iInter₂.mpr h⟩)
    exact ⟨x,hK,mem_iInter.mp hx⟩
end YM.PositionX.Rank
