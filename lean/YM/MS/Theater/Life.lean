import YM.MS.Theater.Eq
/-!
# Differential dual Plane one-jet map. Exact image computed relative onShell only.
Pair conventions Koszul. Readers project physical OPE only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{k h i r n:ℕ} {p:FourP}{b:Bool}
abbrev Look (G:Gauge)(h:ℕ):= RealP (Feet G h)
-- powers
abbrev valueC (Q:Look G h)(b:Bool)(x : Lane4 G): ℂ:= match x with
    | (((some i,c),a),p)=> if c=b then item i Q a p else 0
    | _=>0
def shutter (G:Gauge)(h:ℕ)(b:Bool): Look G h→ₗ[ℂ] Grade G:={
    toFun f:= valueC f b
    map_add' f g:= by funext i; rcases i with ⟨⟨⟨_|i,c⟩,a⟩,p⟩; exact (zero_add _).symm; unfold valueC; simp only [ Pi.add_apply, valueC ]; split; exact mul_add ..; simp
    map_smul' z f:= by funext i; rcases i with ⟨⟨⟨_|i,c⟩,a⟩,p⟩; exact (mul_zero _).symm; unfold valueC; simp only [ Pi.smul_apply,valueC,smul_eq_mul]; split; exact mul_left_comm ..; exact (mul_zero _).symm }
abbrev StarView (h:ℕ)(b:Bool)(X: Look G h): Grade G := shutter G h b X
-- find weight.
lemma seedA (X: Look G h): StarView h false X∈ yields (h+1) 0:= by
    refine seedStar.mpr ⟨?_,?_⟩; · rintro ⟨⟨_|i,_|_⟩,t⟩ <;> first| exact form_zero _| convert! portθ X i t using 1; rw [show mslug ((some i,false),t)=1 from rfl, add_sub_cancel_right]
    rintro ⟨⟨⟨_|i,_|_⟩,a⟩,p⟩ hx <;> first | rfl| exact ( hx rfl ).elim
lemma seedB (X: Look G h): StarView h true X∈ yields (h+3) (-1):= by
    refine seedStar.mpr ⟨?_,?_⟩; · rintro ⟨⟨_|i,_|_⟩,t⟩ <;> first| exact form_zero _| convert! portθ X i t using 1; rw [show mslug ((some i,true),t)=3 from rfl, add_sub_cancel_right]
    rintro ⟨⟨⟨_|i,_|_⟩,a⟩,p⟩ hx <;> first | rfl| exact ( hx rfl ).elim
lemma quietly {X:Look G h}: shutter G h b X=0→ X=0:= by
   intro hP; apply select; intro j; funext k p; obtain hc:= congr_fun hP (((some j,b),k),p); change ( if b=b then item j X k p else 0 )=_ at hc; rw [if_pos rfl] at hc; unfold item at *; rw [hc]; exact (mul_zero _).symm
lemma lift_inj (G:Gauge)(h:ℕ)(b:Bool): Injective (shutter G h b):= by apply LinearMap.ker_eq_bot.mp; apply eq_bot_iff.mpr; intro x hx; exact (Submodule.mem_bot _).mpr (quietly ( LinearMap.mem_ker.mp hx ))
variable {f:Grade G}
lemma tune_K (he:f∈ yields (h+1) 0): ∃ X:Look G h,f=StarView h false X:= by
   let g(a:Axis)(b:G.ColorIndex)(p:FourP):= f (W a b p); have hg a t:Plane.Shape (g a t) (h:ℤ):= by convert! (seedStar.mp he).form (Landau.gauge a,t); rw [show mslug (Landau.gauge a,t)=1 from rfl, add_sub_cancel_right]
   obtain ⟨x,hx⟩:=jetting g h hg; refine ⟨x,?_⟩; funext z; rcases z with ⟨⟨⟨_|a,_|_⟩,i⟩,p⟩ <;> ( first | (refine (seedStar.mp he).real' _ ?_; norm_num [ghostNo,ghostChannel]; done) | exact (congr_fun (congr_fun (hx a) i) p).symm )
lemma turn_K (he:f∈ yields (h+3) (-1)): ∃ X: Look G h,f=StarView h true X:= by
   let g(a:Axis)(b:G.ColorIndex)(p:FourP):= f (U a b p); have hg a t:Plane.Shape (g a t) (h:ℤ):= by convert! (seedStar.mp he).form (Landau.anti a,t); rw [show mslug (Landau.anti a,t)=3 from rfl, add_sub_cancel_right]
   obtain ⟨x,hx⟩:=jetting g h hg; refine ⟨x,?_⟩; funext z; rcases z with ⟨⟨⟨_|a,_|_⟩,i⟩,p⟩ <;> ( first | (refine (seedStar.mp he).real' _ ?_; norm_num [ghostNo,ghostChannel]; done) | exact (congr_fun (congr_fun (hx a) i) p).symm )
-- differentiation linear gauge
variable {X:Look G h}
lemma alphaV (p:FourP)(c:G.ColorIndex): Q ( StarView h false X ) ( C c p )= item () ( X.comp ( gradS G h ) ) c p:= by
    rw [movesC]; unfold item; simp_rw [LinearMap.comp_apply, grad_at,map_sum,map_smul, Finset.mul_sum ]; have he (j:Axis): StarView h false X ( W j c p )= item j X c p:= rfl; simp_rw [ he ]; refine Finset.sum_congr rfl fun i _=> ?_; unfold hitϑ item; push_cast; rw [pow_succ,Complex.real_smul]; ring -- unfold order
lemma capQ (X:Look G h): Q ( StarView h false X )=0↔ X.comp ( gradS G h )=0:= by
   constructor; · intro ht; refine select _ _ (fun _=>?_); ext x p; obtain hk : item () ( X.comp ( gradS G h ) ) x p=0:= Eq.trans ( alphaV p x ).symm ( congr_fun ht (C x p) ); exact hk.trans (mul_zero _).symm
   intro he; funext x; rcases x with ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩
   all_goals first| (change Q _ ( C c p )=0; rw [alphaV, he]; exact mul_zero _)| exact (seedStar.mp (stays _ _ _ (seedA X))).real' _ (by norm_num [ghostNo,ghostChannel])
lemma pair_core (X:Look G h): Q ( StarView h true X )= StarView (h+2) false ( X.comp ( Hess G h ) ):= by
   funext i; rcases i with ⟨⟨⟨_|i,_|_⟩,c⟩,p⟩ <;> first | (apply (seedStar.mp (stays _ _ _ (seedB X))).real'; norm_num [ghostNo,ghostChannel]; done )| skip
   change Q _ (W i c p)= item i ( X.comp ( Hess G h ) ) c p; rw [ movesA ]; unfold item; simp_rw [LinearMap.comp_apply,synth,map_sum,map_smul, Finset.mul_sum ]; refine Finset.sum_congr rfl fun j _=>?_ ; change - _ * item j X c p = _; unfold item hitϑ; rw [Complex.real_smul,pow_add,Complex.I_sq,realK i j]; push_cast; ring
end YM.MS.Theater
