import YM.FVA2.Extras.Bright
import YM.FVA2.Extras.Polynomial
/-! # `First`: leading-order/letter-number calculations for Forth

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
variable {I:Type}{G:Gauge}{B:Deck G}{K:Booked B}{M:MS_Data G K}{F:Glade G Unit}
variable {b d:ℤ}{r k n:ℕ}{u t:ℝ}{X Y:T ( Glade G Unit )}
abbrev localX (G:Gauge):= Glade G Unit
abbrev Quiet (X:T ( localX G )) (i:ℕ):Prop:= ∀ j< i, X j=0
-- exact two-sided Taylor recognition at this order/rank
structure First (F:T (localX G))(u:ℝ)(t:ℤ)(d r:ℕ): Prop where
    calm : Quiet F d
    finance: Clean u (F d) t
    limit: Diversity (F d) r
abbrev Narrow (F:T (localX G))(d r:ℕ)(t:ℝ) : Law G:= Book.mask r ( F d () t )
lemma together (e:Signal.Pair (localX G))(hp:Quiet X k) (hX:Lives.gather M (logMass u)=Y): pairW e Y X k=0:= by
    rw [← hX, paired]; apply Finset.sum_eq_zero; intro i hi; by_cases he:i.1=0; rw [ he,zero_B M,map_zero,LinearMap.zero_apply ]; rw [ hp i.2 (by obtain h:= Finset.mem_antidiagonal.mp hi; omega),map_zero]
lemma First.flat (h:First X u d k r)(H:Response X M (logMass u) b): Narrow X k r t=Narrow X k r 0:= by
    have hx:helm M (logMass u) X k=(both G Unit).P ( X k ) := by change _+pairW (both G Unit).X (Lives.gather M (logMass u)) X k= _; rw [together ( k:=k ) (M:=M) (u:=u) _ h.calm rfl,add_zero]; rfl
    have hv:= H.vital k; rw [hx] at hv; ext l; by_cases hm: l.length = r; swap; · rw [Narrow,Narrow,strange _ (by omega),strange _ (by omega)]
    rw [Narrow,Narrow,enough _ (by omega), enough _ (by omega) ]; have h0(s:ℝ): HasDerivAt (fun t=> X k () t l) 0 s:= by rw [← show (both G Unit).P ( X k ) () s l=0 from cdrop ( H.life k|>.cross ) h.limit realityA () s l (by omega) ]; exact hv () s l
    exact is_const_of_deriv_eq_zero (fun s=>(h0 s).differentiableAt) (fun s=>(h0 s).deriv) t 0
-- lease basis membership
abbrev Watcher (G:Gauge):= Charge ( Landau.parity ( A:=Axis ) ( C:=G.ColorIndex ) ) QP ℂ
lemma rentQ (V:Law G): natQ (Book.mask r V)= Book.mask r (natQ V):= by
    ext w; by_cases hx:w.length=r
    · rw [enough _ (by omega),natQ, visit_Z,visit_Z]; apply visit_agree; intro l i j hj; apply Finset.sum_congr rfl; intro z _; rw [enough _ (by simp only [ ← hj,List.length_append,List.length_cons ] at hx; simp; omega)]
    rw [strange _ (by omega)]; exact rankQ ( X:=Book.mask r V ) (fun i _ h'=> strange _ (by omega)) w (fun i=>Bool.noConfusion i) hx
lemma First.sees (h:First X u d k r)(H:Certified X M (logMass u) b): natQ ( Narrow X k r 0 )=0:= by
    have hp: (both G Unit).J ( X k )=0:= by
       rw [← show nav M (logMass u) X k=_ from (by change _+pairW (both G Unit).C (Lives.gather M (logMass u)) X k= _; rw [ together ( k:=k ) (M:=M) (u:=u) _ h.calm rfl,add_zero ]; rfl : nav M (logMass u) X k=(both G Unit).J (X k) )]; exact congr_fun H.2 k
    rw [front,LinearMap.add_apply] at hp; rw [Narrow,rentQ,show natQ (X k () 0)= _ from congr_fun (congr_fun (eq_neg_of_add_eq_zero_left hp) ()) 0, Pi.neg_apply, Pi.neg_apply, map_neg, Menus.maskOff (by omega : ((r:ℤ)-2)< (r:ℤ)) (cdrop ( H.1.life k |>.cross ) h.limit realityB () 0),neg_zero]
lemma First.form (h: First X u d k r)(H:Response X M (logMass u) b): Narrow X k r 0 ∈ Local.Physical.Lease G d r b:= by
    refine lease_one.mpr ⟨ plank ( H.life _|>.tone _ _ ),?_, fun l _ hp=> strange _ (by omega)⟩; intro E _ _ w _; by_cases hr:w.length=r
    swap; · rw [show fieldVal _ _=0 from funext fun i=> strange (sail w i) (by rw [sail_len]; omega)]; exact form_zero _
    let g:=fieldVal (Narrow X k r 0) w; have he:= h.finance E w (fun x=>Bool.noConfusion x) (fun x=>Bool.noConfusion x); unfold Cape at he
    rw [ show Chart _ w=(fun _=>g) from funext (fun (x:ℝ)=> funext (fun p=>?_)) ] at he; swap; · unfold g; rw [← h.flat (t:=x) H ]; exact ( enough (F:= X k () x) ( sail w p ) (by rw [sail_len]; exact_mod_cast hr ) ).symm
    refine Sharp.shape (u:=u) ?_ (he.smooth 0); intro m; obtain ⟨C,hC,b,hb⟩:= he.quoted m; refine ⟨ C,hC,b,fun p t=> le_trans (hb t p trivial) (le_of_eq ?_)⟩; refine congr_arg (C*_ *·) ?_; change exp t ^pitch w*exp t ^(-d)*exp t ^m=exp _; rw [← zpow_natCast (exp t) m, ← zpow_add₀ (exp_pos t).ne', ← zpow_add₀ ( exp_pos t ).ne', show t*(( m:ℝ )-↑(d-fieldDim wfield w))=t*((pitch w+ -d+(m:ℤ) :ℤ):ℝ) from (by unfold pitch; push_cast; ring),exp_mul,Real.rpow_intCast]
end YM.FVA2.Extras
