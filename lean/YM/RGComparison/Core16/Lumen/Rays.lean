import YM.RGComparison.Core16.Lumen.Needle
/-! # Real unary perturbative force law

Inverse times-charge: no extra correction rows hidden (untaxed stage conversion in Grace/Bounce).
Use printed shelf charge incl external linear offset! θ integrated SS once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Gravity
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals Matrix
open PertExtension PertExtension.Series Tested Radial Therm
open Stage Finset Planet
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}(P:Planet X S ι k T) (i:Wire G ι)

def tether (i:k)(a: Wire G ι):= shelfH X (P.glyph i) (P.ray i,0) (P.tip i a)
def tilt:= ∑ a∈P.within i.1, tether P a i
variable {P} (H:P.Steady) {b:ContDiffBump (0:ℝ)} (hb:Dust b X.δ)

omit [Fintype ι] [Fintype k] [Fintype T] in
lemma portions (a:k) (x:Sky G ι)(g:ℝ): (incision G D) (book (path P i a) g x)=(P.ray a,0)+ P.marks a (vector (fun i=> tally g i x)):=by
    rw [P.mark_price]; refine Prod.ext (show _=_ from ?_) ?_
    · rw [Prod.mk_add_mk,add_zero]; rfl
    funext j; rw [Prod.mk_add_mk,zero_add]; change book (path P i a) g x (.inr j)=portrait (P.stem a) _ j; unfold portrait book path; dsimp only [Sum.elim_inr]; cases h:P.stem a j with
    | none=> rfl
    | some u=> ext r; simp [tally,Option.elim_some,vector,div_eq_mul_inv,curve,mul_comm]
include H
lemma unpaid (g:ℝ)(x:Sky G ι) (a:k) : Error 2 (weight P i b a) (recipe X (P.glyph a,P.hint a i.1,i.2)) (path P i a) g x = P.dark b i x* P.drizzle i a g x - g*(tether P a i + ∑ q,shelfH X (P.glyph a) (P.tip a i) (P.tip a q)*tally g q x):=by
    let Z:= (P.glyph a,P.hint a i.1,i.2); let p:= path P i a; let F:= X.U (P.glyph a); let v := fun q => tally g q x
    let Q:=tale p (recipe X Z)
    have hq : Q 0 g x=0:=by rw [show Q 0 g x = recipe X Z 0 from jet_zero ..]; unfold recipe; rw [map_zero, (H.prices.first _).fderiv]; rfl
    have he : Q 1 g x=tether P a i+∑q,shelfH X (P.glyph a) (P.tip a i) (P.tip a q)* v q :=by
       unfold Q tale p; rw [gravity_jet H.prices Z, portions,show _ = P.tip a i from (P.hint_eq i a),map_add,_root_.add_apply]; congr 1
       rw [P.inventory]; simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]; refine sum_congr rfl ?_; intro j hj; change v j * _= _; rw [mul_comm (v j)]; congr 1; apply (higher H.prices (P.glyph a)).isSymmSndFDerivAt_of_omega -- computational
    change P.dark b i x* _ - untilB (fun i=> Q i g x) 2 g= _
    unfold untilB; rw [Finset.sum_range_succ,Finset.sum_range_one]; simp only [hq,pow_one,pow_zero,he,v,mul_zero,zero_add]
lemma impending (b:ContDiffBump (0:ℝ))(g:ℝ)(x:Sky G ι): ∑ a∈ P.within i.1,Error 2 (weight P i b a) (recipe X (P.glyph a,P.hint a i.1,i.2)) (path P i a) g x=
     P.dark b i x*P.attr i g x-g*(tilt P i+∑ j,P.plank i j*tally g j x):=by
    let U:=P.within i.1; let T:= (shelfH X); let L (a:k)(j:Wire G ι):= T (P.glyph a) (P.tip a i) (P.tip a j) * tally g j x
    simp_rw [unpaid i H]; rw [sum_sub_distrib]; simp only [tether,← mul_sum,Planet.attr,sum_add_distrib,tilt]; congr 3
    rw [Finset.sum_comm]; refine sum_congr rfl (fun j _=>?_); unfold Planet.plank; rw [Matrix.of_apply, sum_mul]; exact sum_subset (subset_univ _) fun a _ he=> by
        rw [tip_absent H a i (by rwa [P.in_heat]), map_zero]; change 0*_=_; rw [zero_mul]

variable (P)
-- Actual mixed Planar (posterior). Not P.c.P.Frame row.
def lamp_gap (b:ContDiffBump (0:ℝ))(w:Rail G ι)(s:ℝ):ℝ:=
   let g:= dollar s
   P.expect g (fun x=> sing w g x*(P.dark b i x* P.attr i g x/g)) -
    (tilt P i*P.expect g (sing w g) + ∑ j,P.plank i j * P.expect g (sing (j::w) g))
omit H -- reinclude using implicit P ?
variable {P}[Fintype A]
include H
omit [Fintype A] in
lemma taxes {C:ℝ}(h:∀ a∈P.within i.1, Visible X (recipe X (P.glyph a,P.hint a i.1,i.2)) (weight P i b a) (path P i a) (patchN X.sector) C) (s:ℝ) (he:amen X (dollar s))(w:Rail G ι) : lamp_gap P i b w s= ∑ a∈ P.within i.1, (lapse P 1 (path P i a) (recipe X (P.glyph a,P.hint a i.1,i.2)) (weight P i b a) w s):=by
    let g:=dollar s; let Z:= P.dark b i* P.attr i g; let Q:= tilt P i; let f:= sing w g; let U:=P.within i.1
    let R (a:k) := Error 2 (weight P i b a) (recipe X (P.glyph a,P.hint a i.1,i.2)) (path P i a) g
    let v (a:k) := g⁻¹ • (f * R a); let t (x: Sky G ι) := f x*(Z x/g); let W (j:Wire G ι):= P.plank i j • sing (j::w) g
    have hV : ∑ a∈ U, v a = t-(Q • f+∑ j,W j):=by
        funext x; have H₀:= impending i H b g x; simp only [Finset.sum_apply, Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.sub_apply,v,Pi.mul_apply]; simp_rw [←mul_sum]; change g⁻¹ * (f x * (∑a∈U,R a x))= f x*(Z x/g)- _ ; rw [show ∑ a∈U,R a x= _ from H₀]; simp_rw [W, Pi.smul_apply, sing_cons, smul_eq_mul, ← mul_assoc,← sum_mul]; unfold Z; rw [Pi.mul_apply]; unfold f Q; have hg:0<g:=dollar_pos _; field_simp
    have eh:Envelope f:=havenreal (sing_cont ..)
    have Ht:Envelope t:=by unfold t; simp_rw [div_eq_mul_inv]; exact eh.mul (((P.whirl b i).1.mul (havenreal (stout i H g))).mul (.const _))
    have hy j: Continuous (W j) := continuous_const (y:= P.plank i j)|>.smul (sing_cont ..)
    have hL : ∑ a∈ U, lapse P 1 (path P i a) (recipe X (P.glyph a,P.hint a i.1,i.2)) (weight P i b a) w s=P.expect g (∑ a∈U,v a) :=by
        rw [paid H he U _ (fun a ha=> show Envelope (v a) from (Envelope.const _).mul (eh.mul (Error.literacy H (h a ha) he 2)))]; refine sum_congr rfl (fun a _=>?_); unfold v lapse; rw [P.expect_mul,pow_one]
    have Hq: Envelope (∑ j,W j):=havenreal (by rw [show ∑ j,W j=fun x=>∑ j,W j x from funext fun x=> Finset.sum_apply ..]; exact continuous_finsetSum _ fun j _=>hy j)
    rw [hL,hV, expect_sub H he (f:=t) (f':= Q • f +∑ j,W j) Ht ?_, expect_add H he (f:=Q • f) _ _]; rotate_left
    · exact (Envelope.const _).mul eh
    · exact Hq
    · exact Envelope.add ((Envelope.const Q).mul eh) Hq
    rw [P.expect_mul,paid H he _ _ (fun j _=>havenreal (hy j))]; simp_rw [W, Planet.expect_mul]; rfl
omit H
lemma elevator (Y:Good X)(r d:ℕ)(B:Stage)(u:ℝ)(hu:0≤u) :∃ (U:Stage)(v:ℝ), U.Above B ∧ Visit U X ∧ 0≤v ∧ ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T) (n:Side)(P:Planet X n ι k T),P.Steady→ ∀ b:ContDiffBump (0:ℝ),Dust b X.δ→ Raw P B r (1+r+d) u→∀ i w,w.length≤d→ U.Ticket (r+1) v (lamp_gap P i b w):=by
    obtain ⟨C,hC,h⟩:= need_cost Y; obtain ⟨U,v,hU,hV,hv,hh⟩:= accrue Y (recipe X) (fun i=>(fatigue Y i).of_le le_top) r 1 (patchN X.sector) d hC hu B
    refine ⟨U,weights X.sector X.sector.b*v,hU,hV,mul_nonneg (weights_pos ..|>.le) hv,fun ι k T _ _ _ n P H b hb hp i w hd=>?_⟩
    have hx a (ha:a∈P.within i.1) := h ι k T _ _ _ n P H b hb i a ha
    let F a:= lapse P 1 (path P i a) (recipe X (P.glyph a,P.hint a i.1,i.2)) (weight P i b a) w; let I:=P.within i.1
    refine ((U.ticket_sum (r+1) I F (fun _=>v) (fun j hj=> hh ι k T _ _ _ n P H hp _ _ _ (hx j hj) w hd)).reload (fun s hs=> (taxes i H hx s (hV s hs) w).symm)).promote ?_
    rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (price_cover (loc:=P.root) ((H.tickets 0 ⟨le_refl _,Y.thick.2.1.le⟩).edge) _ _)) hv
include H
lemma offset_cost : |tilt P i| ≤ weights X.sector X.sector.b *(Planet.ferris X * X.Q):=by
    refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>Planet.ferris X * X.Q) (fun a _=>?_)).trans ?_)
    · have hf : ‖shelfH X (P.glyph a)‖ ≤ Planet.ferris X:= single_le_sum (fun i _ => norm_nonneg (shelfH X i)) (mem_univ _)
      have hg: ‖(P.ray a,(0:D→G.Color))‖ ≤ X.Q:=by rw [Prod.norm_def]; simp [H.priced a]
      exact ((((shelfH X (P.glyph a)) _).le_of_opNorm_le_of_le ((shelfH X (P.glyph a)).le_of_opNorm_le_of_le hf hg) (tip_cost (P:=P) a i)).trans_eq (mul_one _))
    rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (price_cover (loc:=P.root) ((H.tickets 0 ⟨le_refl _,H.prices.thick.2.1.le⟩).edge) _ _)) (mul_nonneg ferris_nn H.prices.thick.1.le)
end YM.RGComparison.Core16.Lumen.Gravity
