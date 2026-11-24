import YM.RGComparison.Core16.Lumen.Hike

/-!
# The common TICKET given bootstrap on same precision but shorter words & smaller precision but LONGER
words. Both on this conditional call. No mark extraction on a future yr needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Gravity
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals Matrix
open PertExtension PertExtension.Series Tested Radial Therm
open Stage Finset Planet
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}{P:Planet X S ι k T} {b:ContDiffBump (0:ℝ)}
lemma stamp_due (H:P.Steady) {C : ℝ}{i:Option (G.ColorIndex× G.ColorIndex)}{N:ℕ}{p: Stuff G ι Unit}{f: Melody G ι}(w:Rail G ι)(h:Visible X (wing G i) f p N C) (x:ℝ)(hx:amen X (dollar x)) :
    P.expect (dollar x) (sing w (dollar x)*f (dollar x)) = lapse P 0 p (wing G i) f w x + wing G i 0*P.expect (dollar x) (sing w (dollar x)) := by
    unfold lapse; rw [Error.tribute H h hx]; simp only [pow_zero,one_mul,sum_range_one,Nat.zero_add]; let g:=dollar x
    have hz: ∀ u:Sky G ι, tale p (wing G i) 0 g u=wing G i 0:= fun u=> jet_zero ..
    let z:= wing G i 0; change _= _-P.expect g _ + _* P.expect g _
    rw [show (sing w* tale p (wing G i) 0) _=z • sing w g from ?_, P.expect_mul,sub_add_cancel]
    funext y; change sing w g y * _ = z * sing w g y; rw [hz]; ring

variable (hb:Dust b X.δ)
private abbrev bellWorld := ∑ i: Option (G.ColorIndex× G.ColorIndex), |wing G i 0|

-- both estimates REQUIRE (on top of inductive hypothesis) matching prescription on all SHORTER word-lengths
include hb
theorem distill (r d:ℕ){v u:ℝ}(Y:Good X)(M:Stage) (hv:0≤ v)(hu:0≤ u):∃ (D:ℝ)(T:Stage), 0≤ D ∧ T.Above M ∧ Visit T X ∧ ∀ (ι k U:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype U)(n:Side)(P:Planet X n ι k U), P.Steady → Raw P M r (1+r+d) u → Raw P M (r+1) d v→∀ i:Wire G ι, ∀ w:Rail G ι,w.length≤d→
       T.Ticket (r+1) D (fun x=> P.expect (dollar x) (sing w (dollar x) * fove P i b (dollar x))) ∧
       ∀ j,T.Ticket (r+1) D (fun x=> P.expect (dollar x) (sing w (dollar x)*belt P i j b (dollar x))):=by
    obtain ⟨z,hz,h⟩:= sky hb Y
    obtain ⟨T,t,hT,he,ht,W⟩:= accrue Y (wing G) wing_smooth r 0 (patchN X.sector) d hz hu M
    let A:= @bellWorld G; have hA:0≤A:=sum_nonneg fun _ _=> abs_nonneg _
    refine ⟨t+A*v,T,by positivity,hT,he,fun ι k U _ _ _ n P H h1 h2 i w hw=>?_⟩
    have hx:= h ι k U _ _ _ n P H i
    have hR j f (hf:Visible X (wing G j) f (guide i) (patchN X.sector) z) : T.Ticket (r+1) (t+A*v) (fun x=> P.expect (dollar x) (sing w (dollar x) * f (dollar x))) := by
       have hv':= W ι k U _ _ _ n P H (Raw.broaden h1 above_refl (le_refl _) (by omega)) j f (guide i) hf w hw
       have hh: |wing G j 0| ≤ A:= single_le_sum (f:=fun i =>|wing G i 0|) (fun _ _=>abs_nonneg _) (mem_univ _)
       refine ((hv'.more ((h2 w hw).extend hT |>.scales (wing G j 0))).promote (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hh hv))).reload (fun x hm=>?_)
       exact (stamp_due H w hf x (he x hm)).symm
    exact ⟨hR _ _ hx.1,fun j=>hR _ _ (hx.2 j)⟩

omit hb
variable (i:Wire G ι) {r d:ℕ}{M : Stage}{v u:ℝ}
-- support in first marker leg & all word ordering duplicates.
private lemma invoice (H:P.Steady) (W:Visit M X) (hv:∀ w:Rail G ι,w.length≤d→∀ j, M.Ticket (r+1) v (fun x=>P.expect (dollar x) (sing w (dollar x)*belt P i j b (dollar x)))) :
   ∀ w w':Rail G ι, w.length+w'.length ≤ d → M.Ticket (r+1) ((w.length:ℝ)*v) (fun x=> P.expect (dollar x) (sing w' (dollar x) * P.dark b i * depart i (dollar x) w)):=by
    intro w; induction w with
    | nil=> simp only [List.length_nil, Nat.zero_add,Nat.cast_zero,zero_mul,depart, mul_zero]; intro v hv; exact (M.ticket_zero _).reload (fun x hx=> (burden H (W x hx) 0).symm)
    | cons j w h=>
       intro t ht
       have he: (t++w).length ≤ d:=by simp; simp only [List.length_cons] at ht; omega
       have hK : w.length+(j::t).length ≤ d:=by simp at *; omega -- risk
       have hh := hv (t++w) he j; have hR:=hh.more (h (j::t) hK)
       rw [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm _ v]
       refine hR.reload (fun x hx=>?_) ; let g:= dollar x
       let f:=sing (t++w) g * belt P i j b g; let d':=P.dark b i; have eh:=P.whirl b i|>.1
       let s:=sing (j::t) g * d' *depart i g w
       have hf:Envelope f:= (havenreal (sing_cont ..)).mul (eh.mul (havenreal (paper_cont ..))); have hs:Envelope s:= (((havenreal (sing_cont ..)).mul eh).mul (havenreal (depart_cont ..)))
       change P.expect g f+P.expect g s=P.expect g _; rw [← expect_add H (W x hx) hf hs]; congr 1; ext y; simp [s, belt,f,depart,sing_cons,sing_join]; unfold d'; ring

private lemma pull (H:P.Steady) {g:ℝ}(_hg:amen X g)(f: Sky G ι→ ℝ)(hf:Envelope f) : Envelope (fun x=> f x * (P.dark b i x * P.attr i g x / g)):= by simp_rw [div_eq_mul_inv]; exact hf.mul (((P.whirl b i).1.mul (havenreal (stout i H g))).mul (.const _))
include hb
lemma duty (H:P.Steady){g:ℝ}(h:amen X g)(hg:0<g)(w:Rail G ι):
    P.expect g (fun x=> sing w g x *(P.dark b i x * P.attr i g x/g))= P.expect g (P.dark b i*depart i g w) + P.expect g (sing w g * fove P i b g) :=by
    let p:=P.dark b i; let f:=sing w g; let V (x : Sky G ι):= f x*(p x*P.attr i g x/g); let W:=fove P i b g
    let U:= depart i g w; have hx:=P.whirl b i; have he: Envelope f:= havenreal (sing_cont ..); have hh :Envelope U:= havenreal (depart_cont ..)
    have hP:Envelope (p*U+f*W):= Envelope.add (hx.1.mul hh) (he.mul ((Envelope.const _).mul hx.2)); have hV: Envelope V:= pull i H h f he
    have hp : V-(p*U+f*W)= P.scope g i b f U:= funext fun x=> by change f x* (p x* _ / _) - (p x*U x+f x * (g*P.faint b i x))=p x*_* f x/g-p x*U x - _; ring
    rw [← expect_add H h (f:=p*U) (f':=f*W) (hx.1.mul hh) (he.mul ((Envelope.const _).mul hx.2)), ←sub_eq_zero, ← expect_sub H h hV hP,hp]; exact breathed H h i hb hg (fun x=> currents i g x w) he hh

omit hb in
lemma dpose (H:P.Steady) (W:Visit M X) (he:0≤v) (hv:∀ w:Rail G ι,w.length≤ d→∀ j, M.Ticket (r+1) v (fun x=>P.expect (dollar x) (sing w (dollar x)*belt P i j b (dollar x)))) (w:Rail G ι)(hh:w.length≤ d): M.Ticket (r+1) (d *v) (fun x=>P.expect (dollar x) (P.dark b i*depart i (dollar x) w)):=by
    refine ((invoice i H W hv w [] (by simpa)).promote (mul_le_mul_of_nonneg_right (by exact_mod_cast hh) he)).reload ?_
    intro x hx; change P.expect _ (_*_*_) = _; rw [show sing (G:=G) (ι:=ι) [] (dollar x)=1 from rfl,one_mul]
end YM.RGComparison.Core16.Lumen.Gravity
