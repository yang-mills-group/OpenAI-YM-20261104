import YM.FVA2.O.Rough.Large
/-!
# Absolute sizes for border and tree
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Rough
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open scoped Topology ContDiff Interval
variable {E F J I:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {x y a:I→ℝ}{n m:ℕ}{S:Scale I}
variable {G:Gauge}{X Y:I→Law G}{U:I→Edge G}
omit [NormedSpace ℝ E] in
lemma lump {p: Sector F} (l:Legs F){f:I→ E→ Shared F ℂ}(h:∀ a b, Split a b l → Size S.full (fun i p=> f i p a b) (fun i _=> x i)): Size S.full (fun i x=> scatter p l ( f i x ) ) (fun i _=> x i):= by
    induction l generalizing f with
    | nil=> exact h _ _ .nil
    | cons i l ih=> exact ih (fun a b hv=> Size.plus ( h _ _ hv.left ) ( Size.drive ( h _ _ hv.right ) _ ))
lemma branch_q (hp:Lease true true S X x)(hy:FormP S Y y true)(hv:CourseK S a U)(ha:nn a)(hx:nn x)(he:nn y): FormP S (fun i=> tree parity ( U i ) ( X i ) (Y i)) (positive S 4 a (x*y)) false:= by
    intro E _ _ w hw; unfold Tax Plane.Chart tree; simp_rw [sail_scatter,attaches,sail_degree,sail_net]; apply lump; intro l r hl;
    have H1(v:BH G)(c:ℂ):= ( hp E ((v,-net l)::l) (fun _=>by simp) (fun _=>by simp) |>.L (ContinuousLinearMap.mul ℝ ℂ c)|>.norm_cost ); have H2(v:BH G):= hy E ((v,net l)::r) (fun _=>by simp)
    have hm(i j v u:BH G)(h:wfield i+wfield j=wfield v+wfield u)(k:I): S.length k ^ ((4:ℤ)-wfield i-wfield j)*a k*(S.length k^(wfield v+ pitch l)*x k*(S.length k^(wfield u+pitch r)*y k))= Qbud w S (positive S 4 a (x*y)) k:= by
       unfold Qbud positive; simp only [Pi.mul_apply]; have ht:= w_mass hl; conv_rhs=> rhs; arg 1; rw [show S.length k^4= S.length k^(4:ℤ) from rfl];
       have hV: S.length k^((4:ℤ)-wfield i-wfield j)* S.length k^(wfield v+pitch l)* S.length k^(wfield u+pitch r)= S.length k^pitch w*S.length k^ (4:ℤ):= by rw [ ← zpow_add₀ (S.pos k).ne', ← zpow_add₀ (S.pos k).ne',← zpow_add₀ (S.pos k).ne' ]; congr 1; omega
       rw [← mul_assoc (S.length k ^ pitch w) (S.length k ^(4:ℤ)),← hV]; ring -- fix
    have hQ : S.full.NN (fun i (_:E)=>Qbud w S (positive S 4 a (x*y)) i):= fun i _ _=> mul_nonneg ( length_p .. ) ( np S ( joy hx he ) ha 4 i ); refine Size.tally Finset.univ (fun i _=> Size.tally Finset.univ (fun j _=> ?_) hQ) hQ; refine Size.plus ?_ ?_; simp only [neg_neg]; -- use conversions
    · convert! ( Size.fork (( Bound.linear ( -net l ) ( hv i j ) ).norm_cost ) ( Size.fork ( H1 i (cross (parity j) (degree (field parity) l)) ) ( H2 j ) ) ) using 1; ext k p; exact Eq.symm ( hm i j i j rfl k )
    · convert! ( Size.fork (( Bound.linear ( net l ) ( hv i j ) ).norm_cost) ( Size.fork ( H1 j (cross (parity i) ( parity j ^^ degree (field parity) l )) ) ( H2 i ) ) ) using 1; · funext l p; simp only [neg_neg]; rfl
      ext k p; exact Eq.symm ( hm i j j i (add_comm ..) k )
lemma FormP.product (hx:FormP S X x false)(hp:FormP S Y y false): FormP S (fun i=> Koszul.product (field parity) (X i) (Y i)) (x*y) false:= by
    intro E _ _ w hw; unfold Tax Chart; simp_rw [scattered,sail_scatter]; apply lump; intro l r hl; refine Size.mon (Size.fork ( hx E l (fun i=>Bool.noConfusion i) ) (hp E r (fun i=>Bool.noConfusion i))) (Cost.of_le fun i p _=>?_ ); unfold Qbud; rw [ ← w_mass hl,zpow_add₀ (S.pos i).ne' ]; simp only [Pi.mul_apply]; exact le_of_eq (by ring)
end YM.FVA2.O.Rough
