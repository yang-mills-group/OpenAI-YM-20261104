import YM.Integration.WilsonIndependentConditionalMerShift

/-! Positive angular coefficients of a finite ordinary action suffice
for its normalized marked response. The retained source includes rank zero. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalCappedBlue
open Matrix WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {I:Type}[Fintype I]{d:ℕ}
abbrev Positive (P Q:Gen ℝ I):Prop:=∀r,0<r→P r=Q r

omit [Fintype I] in
private theorem cut {P Q:Gen ℝ I}(h:Positive P Q)(a:I):sever a P=sever a Q:=by
  funext r
  simp only [sever,h (r+1) (by omega)]
private theorem line (G:Matrix I I ℝ){P Q:Gen ℝ I}(h:Positive P Q):ripple G P=ripple G Q:=by
  simp only [ripple,cut h]
private theorem join (G:Matrix I I ℝ){P Q R S:Gen ℝ I}(a:Positive P Q)(b:Positive R S):arbor G P R=arbor G Q S:=by
  simp only [arbor,cut a,cut b]
private theorem births (G:Matrix I I ℝ){P Q R S:Layers ℝ I}{k e:ℕ}
    (a:∀j≤k,∀i≤e,Positive (P j i) (Q j i))(b:∀j≤k,∀i≤e,Positive (R j i) (S j i)):
    ravel G P R k e=ravel G Q S k e:=by
  apply Finset.sum_congr rfl;intro v hv
  have h:=Finset.HasAntidiagonal.mem_antidiagonal.mp hv
  apply Finset.sum_congr rfl;intro u hu
  have h':=Finset.HasAntidiagonal.mem_antidiagonal.mp hu
  exact join G (a _ (by omega) _ (by omega)) (b _ (by omega) _ (by omega))

theorem quiet (G:Matrix I I ℝ){V U:ℕ→ Gen ℝ I}(v:∀e≤d,Positive (V e) (U e))(k:ℕ):
    ∀e≤d,Positive (abr G V k e) (abr G U k e):=by
  induction k using Nat.strong_induction_on with
  | h k ih=>
    cases k with
    | zero=>simpa only [abr_zero] using v
    | succ k=>
      intro e he r _
      rw [abr_next,abr_next,line G (ih k (by omega) e he),
        births G (fun j hj i hi=>ih j (by omega) i (by omega)) (fun j hj i hi=>ih j (by omega) i (by omega))]

theorem marked (G:Matrix I I ℝ){V U F W:ℕ→ Gen ℝ I}(v:∀e≤d,Positive (V e) (U e))
    (w:∀e≤d,F e=W e)(k:ℕ):∀e≤d,bul G (abr G V) F k e=bul G (abr G U) W k e:=by
  induction k using Nat.strong_induction_on with
  | h k ih=>
    cases k with
    | zero=>simpa only [bul_zero] using w
    | succ k=>
      intro e he
      have v' (j:ℕ)(_:j≤k)(i:ℕ)(hi:i≤e):Positive (abr G V j i) (abr G U j i):=quiet G v j i (by omega)
      have f' (j:ℕ)(hj:j≤k)(i:ℕ)(hi:i≤e):Positive (bul G (abr G V) F j i) (bul G (abr G U) W j i):=by
        rw [ih j (by omega) i (by omega)];exact fun _ _=>rfl
      rw [bul_next,bul_next,ih k (by omega) e he,births G v' f',births G.transpose v' f']

end YM.Integration.WilsonIndependentConditionalCappedBlue
