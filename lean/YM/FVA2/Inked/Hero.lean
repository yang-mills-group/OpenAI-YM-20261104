import YM.FVA2.Inked.Mixed
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Position.Browse
/-!
 # Word-cost for classical-analytic symbols
    Real exponentials on all space (test family, **not** a global test function for distributions),
    carrying finite lists of modes. See `Play`, `Active`. Compute derivatives of smooth
    germ at zero field and at the base point. Use ℝ exponential (no complex param
    inside sampled fields); Momentum `$i$` extracted via homog dimension.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked
open Function Filter Set Finset Topology
open scoped ContDiff BigOperators Classical
open Lattice RG Maxwell Gen
open MS MS.Koszul MS.Plane MS.Native MS.Native.Draft MS.Cylinder.Taylor MS.Momentum MS.Theater
open MS.Color MS.Arts MS.Motif MS.Landau MS.Landau.Detect MS.Halo MS.Book MS.Heat
open Position.OpenAxis
variable {E J V X : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m n d:ℕ}{G:Gauge}
local notation "P"=> E4
local notation "L"=> Lane4 G
local notation "T"=> E × P
local notation "I"=> Complex.I
-- test wave for leg directions
structure Play (E:Type)[Zero E](G:Gauge) where
   shots:Lane4 G → E
   knows : Set (Lane4 G)
   ghost i : Ψ G 0 i=true → shots i=0
abbrev Active {E:Type}[Zero E]{G:Gauge}(A:Play E G)(w:Legs ( Lane4 G )) : Prop:=∀ i∈w,i∈ A.knows
-- camera type Real exponentials over unscaled Euclidean momenta.
private abbrev bearing (p:FourP) : P→L[ℝ]ℝ:= innerSL ℝ (fixF p)
abbrev flying (x:E4)(p:FourP): ℝ:= Real.exp (lampX x p)
theorem flight_C (p:FourP): ContDiff ℝ ω (fun x:E4=> flying x p):= ( bearing p ).contDiff.exp
lemma flight_s (x:E4)(p q:FourP): flying x (p+q)=flying x p*flying x q:=by unfold flying lampX; rw [map_add,inner_add_left,Real.exp_add]
@[simp] lemma flight_zero (x:E4): flying x 0=1:= by simp [flying,lampX]
@[simp] lemma flight_at (p:FourP): flying 0 p=1:= by simp [flying,lampX]
lemma flight_head (v p:E4)(q:FourP): par v (fun x:P=> (( flying x q :ℝ ):ℂ)) p=(( flying p q*lampX v q:ℝ ):ℂ):=by
    let vQ:= Complex.ofRealCLM; obtain he: ContDiff ℝ ∞ (fun x:E4=> flying x q):= ( flight_C q ).of_le le_top; let D:=bearing q; let X(z:E4):=flying z q; change par v (vQ ∘ X) p=_; rw [ show par v _ p= vQ (par v X p) from par_L (f:=X) vQ ( he.differentiable (by simp) p ) ]; unfold par; rw [( show HasFDerivAt X _ p from D.hasFDerivAt.exp ).fderiv ]; rfl
-- complex lhs always analytic momentum lift. k=int dimension
variable {h k:ℤ}
structure Hero (A:Play E G)(d:ℤ)(f:E × P→ℝ)(B: Law G): Prop where
   smooth : ContDiff ℝ ω f
   caps : Limit B d
   starts (x:P)(w:Legs (Lane4 G))(hw:Active A w): I^(d-(w.length:ℤ)) * MS.Cylinder.Taylor.ink A.shots (fun y:E=> f (y,x)) w = ( ↑( flying x (net w ) ):ℂ ) * B w
namespace Hero
variable {A: Play E G} {B C: Law G}{f g: E × E4 → ℝ}{w:Legs L}
private lemma pc {c:P}(h: ContDiff ℝ ω f) : germ (fun y:E=> f (y,c)):= ( h.comp (f:=fun y:E=>(y,c)) (contDiff_id.prodMk contDiff_const) ).contDiffAt
lemma zero (d:ℤ): Hero A d 0 0:= by
   refine ⟨contDiff_const, (fun i _=> rfl), fun x w hw=>?_⟩; change I^_*MS.Cylinder.Taylor.ink _ (0:E→ℝ) w=_; rw [ink_zero]; simp
lemma add (hx:Hero A h f B) (he: Hero A h g C): Hero A h (f+g) (B+C):=by
    refine ⟨ hx.smooth.add he.smooth,hx.caps.add he.caps, fun x w hw=>?_⟩; change I^_*MS.Cylinder.Taylor.ink _ ((fun y:E=> f (y,x))+(fun y:E=>g (y,x))) w = _; rw [ink_add _ (pc hx.smooth) (pc he.smooth),Pi.add_apply,Pi.add_apply,mul_add,mul_add,hx.starts x w hw,he.starts x w hw]
lemma smul (c:ℝ)(hx:Hero A h f B): Hero A h (c • f) ((c:ℂ) • B):=by
    refine ⟨ hx.smooth.const_smul c,hx.caps.smul _, fun x w hw=>?_⟩; change I^_*MS.Cylinder.Taylor.ink _ (c • (fun y:E=> f (y,x))) w = _; rw [ink_smul _ (pc hx.smooth), Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,mul_left_comm _ (c:ℂ),hx.starts x w hw,mul_left_comm (c:ℂ)]
lemma sub (hx:Hero A h f B)(he: Hero A h g C): Hero A h (f-g) (B-C):=by simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul,sub_eq_add_neg] using hx.add ( he.smul (-1) ) -- dot order?
lemma sum {f:J→ E×P→ℝ}{F:J→ Law G}(S:Finset J)(h:∀ j∈S,Hero A k (f j) (F j)): Hero A k ( ∑ i∈S,f i ) (∑ i∈ S,F i):= by induction S using Finset.induction_on with| empty=> simp_rw [sum_empty]; exact zero _ | insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add ( ih (fun i hg=> h i (mem_insert_of_mem hg)) )
-- scatter helper.
private lemma inl (w:List J)(p:Set J)(hx:∀ i∈w,i∈p)(a b:List J)(ht:Split a b w): ∀ i∈a,i∈p:=fun i hi=> hx i (( split_perm ht ).mem_iff.mp ( List.mem_append_left _ hi ) )
private lemma birth (w:List L)(c:ℂ)(S:Shared L ℂ): c*scatter (Ψ G 0) w S=scatter (Ψ G 0) w (fun a b=> c*S a b):= (map_smul ( allocate ( Ψ G 0 ) w ) c S ).symm
lemma times (hx:Hero A h f B)(hg:Hero A k g C): Hero A (h+k) (f*g) (product (Ψ G 0) B C):=by
    refine ⟨ hx.smooth.mul hg.smooth,hx.caps.pair hg.caps,fun x w hw=>?_⟩; change I^_*MS.Cylinder.Taylor.ink _ ((fun y:E=> f (y,x))*(fun y:E=> g (y,x))) w= _; rw [ink_mul A.shots A.ghost (pc hx.smooth) (pc hg.smooth), scattered,scattered,birth,birth]; apply scatter_congr; intro a b H; have he:= hx.starts x a ( inl w _ hw a b H ); have hv:= hg.starts x b (inl w _ hw b a (split_comm H) ); have hl:= split_length H; change I^_ * ( _*_)= _ * (B a*C b); rw [ show (h+k-w.length:ℤ)=(h-a.length)+(k-b.length) by omega,zpow_add₀ Complex.I_ne_zero,mul_mul_mul_comm,he,hv,←show net a+net b=net w from split_sum _ H,flight_s]; push_cast; ring
variable {a:Axis}
lemma parL (hx:Hero A h f B): Hero A (h+1) (fun p=> par (basis a) (fun t:P=> f (p.1,t)) p.2 ) ( rowP (n:=0) a B ):=by
    have hf : (fun p:T=> par (basis a) (fun t:P=> f (p.1,t)) p.2)= par ((0:E),basis a) f:= funext (fun p=> ( layerR hx.smooth (basis a) p ).symm )
    rw [hf]; refine ⟨ mixed_par hx.smooth,?_ , fun x w hw=>?_ ⟩; · intro l hl; rw [rowP,moon, hx.caps l (by omega),mul_zero]
    rw [ ← ink_peel A.shots hx.smooth _ w, rowP, moon]; let z:= I^( h-( w.length:ℤ ) ); let y(x:E4):= MS.Cylinder.Taylor.ink A.shots (fun t:E=> f (t,x)) w; let e(x:E4):ℂ:= ↑( flying x (net w) ); have ht := congrArg (fun f:E4→ℂ=> par (basis a) f x) ( ( funext (fun i:P=> hx.starts i w hw) ): ( (fun _=> z)*y)= (fun i:P=> e i * B w) ); -- noncomm par.Units
    have hx1:DifferentiableAt ℝ y x:=( ink_c A.shots hx.smooth w ).differentiable (by simp) _; have hx2 : DifferentiableAt ℝ e x:= ((Complex.ofRealCLM.contDiff (n:=ω)).comp ( flight_C _ ) ).differentiable (by simp) x
    have hh: z * par (basis a) y x = e x * (↑(lampX (basis a) (net w)):ℂ) * B w:= by
       have he (u:ℂ): par (basis a) (fun _:P=>u) x=0:= by simp [par]
       change par _ _ _=par _ (e* fun _=>B w) _ at ht; rw [Gen.par_mul (differentiableAt_const _) hx1,Gen.par_mul hx2 (differentiableAt_const _), he,he, mul_zero,zero_mul,add_zero,zero_add, show par _ e x=_ from flight_head (basis a) x (net w),Complex.ofReal_mul] at ht; exact ht
    unfold Motif.δ; change I^_ * par _ y x=e x*(I* (((net w) a:ℝ):ℂ)*B w); rw [ show (h+1-w.length:ℤ)=1+(h-w.length) from (by omega),zpow_add₀ Complex.I_ne_zero,zpow_one,mul_assoc, show I^(h-(w.length:ℤ))=z from rfl,hh]; unfold lampX; rw [lean_axis]; ring
end Hero
end YM.FVA2.Inked
