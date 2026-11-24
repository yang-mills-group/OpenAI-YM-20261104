import YM.SchemeRG11.Long.Glory
/-! Closure needed for local cluster weaving. Schematic algebra, will consume
 TWICE (top valuation; replacement error). -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open Labels MvPolynomial
open scoped Classical
variable {G: Gauge} {m n:ℕ} {T: Align.Itinerary}
abbrev Ban (G:Gauge):= ℕ → Cover→vellum G
def play (f:Slate)(b:Ban G): Ban G:= fun k x=>f k x • b k x
def castV(p:vellum G):Ban G:=fun _ _=>p
def swift (x:Touch G):Ban G:=fun _ z=>leaf (flex z x)
local notation "D₁" => Atoll.land G
inductive Nest (T:Align.Itinerary):ℤ→Ban G→ Prop where
 | unit:Nest T 0 (castV (G:=G) 1)
 | zero (s:ℤ): Nest T s 0
 | add{x f g}: Nest T x f → Nest T x g → Nest T x (f+g)
 | scale{x y f c}:Nest T x f → Plain T (-y) c → Nest T (y+x) (play c f)
 | mul{x y f g}: Nest T x f →Nest T y g → Nest T (x+y) (f*g)
 | piece{n:ℕ}(a: Touch G):a∈Stepper G n → Nest T (n+1:ℤ) (swift a)
lemma nest_sum {I:Type*} (s:Finset I)(p:I→ Ban G)(n:ℤ)(h:∀i∈s,Nest T n (p i)):Nest T n (∑i∈s,p i):=by induction s using Finset.induction_on with
 | empty=>rw [Finset.sum_empty]; exact Nest.zero _
 | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun i hi=>h i (by simp [hi]))
lemma nest_pile {I:Type*}(s:Finset I)(p:I→Ban G)(n:ℤ)(h:∀i∈s,Nest T n (p i)):Nest T n (fun k x=>∑i∈s,p i k x):=by
 convert nest_sum s p n h using 1; funext k x;simp
lemma nest_c {x:ℤ}{f:Ban G}(h:Nest T x f)(c:ℝ): Nest T x (play (view (fun _=>c)) f):=by
 have he:= h.scale (y:=0) (show Plain T (-0) _ from (show -(0:ℤ)=0 from neg_zero) ▸ Plain.const c); rw [zero_add] at he; exact he
def crew (a:Touch G):Module.End ℝ (Ban G) := LinearMap.pi fun (i:ℕ)=> LinearMap.pi fun (p:Cover)=> ((vent ((D₁).windfall a)).toLinearMap ∘ₗ LinearMap.proj p) ∘ₗ LinearMap.proj i
lemma crews (a: Touch G)(f:Ban G)(i:ℕ)(p:Cover): crew a f i p=vent ((D₁).windfall a) (f i p):=rfl
lemma skid {b:Ban G}{x:ℤ}(h:Nest T x b)(a:Touch G)(m:ℕ)(ha:a∈Stepper G m):Nest T ((m+1:ℤ)+x) (crew a b):=by
 induction h with
 | unit=>rw [show crew a (castV 1)=0 from funext fun i=>funext fun x=>by rw [crews]; apply Derivation.map_one_eq_zero]; exact .zero _
 | zero x=>rw [map_zero]; exact .zero _
 | add h k H K=>rw [map_add]; exact H.add K
 | @scale x y f c h k ih=>
   rw [show crew a (play c f)=play c (crew a f) from funext fun i=>funext fun x=>by rw [crews,play]; exact (vent _).map_smul (c i x) _,add_left_comm]
   exact ih.scale k
 | @mul x y f g h k H K=>
   have hx: Nest T ((m+1:ℤ)+(x+y)) (f*crew a g):=(show x+((m+1:ℤ)+y)=_ from (add_left_comm x (m+1:ℤ) y)) ▸ h.mul K
   have hv: Nest T ((m+1:ℤ)+(x+y)) (g*crew a f):=(show y+((m+1:ℤ)+x)= (m+1:ℤ)+(x+y) by abel) ▸ k.mul H
   rw [show crew a (f*g)=_ from funext fun i=>funext fun p=> show _=(f*crew a g + g*crew a f) i p from vent_l ..]
   exact .add hx hv
 | @piece n u k=>
   let t(z):= (D₁).bed (flex z u) a
   have he:Plain T (-((m+1:ℤ)+(n+1:ℤ))) (view t):=by convert vats (T:=T) k ha using 1; abel
   have eq := (Nest.unit (G:=G) |>.scale he); rw [add_zero] at eq
   convert eq using 1; funext j z; rw [crews,swift,taste]; unfold play view t castV; rw [double_comm]; simp [MvPolynomial.smul_eq_C_mul,Dose.bed]

structure Volume (G:Gauge)(T: Itinerary) where
 classV: ℤ → Ban G → Prop
 nest (v b): Nest T v b → classV v b
 add {v b c}: classV v b →classV v c →classV v (b+c)
 coin (v b)(c:ℝ): classV v b →classV v (fun i p=> c • b i p)
 mul {u v b c}:classV u b→classV v c→classV (u+v) (b*c)
 scale {u v b c}: classV u b → Plain T (-v) c →classV (v+u) (play c b)
 anchor (a:Touch G)(m:ℕ): a∈ Stepper G m→classV (m+1:ℤ) (castV (leaf a))
namespace Volume
variable (V:Volume G T)
lemma sum {I:Type*}(s:Finset I)(p:I→Ban G)(v:ℤ)(h:∀i∈s,V.classV v (p i)):V.classV v (∑i∈s,p i):=by induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; exact V.nest v _ (.zero _)
 | insert i s hi ih=>rw [Finset.sum_insert hi]; exact V.add (h i (by simp)) (ih fun i hi=>h i (by simp [hi]))
lemma piles{I:Type*}(s:Finset I)(p:I→Ban G)(v:ℤ)(h:∀i∈s,V.classV v (p i)):V.classV v (fun k x=>∑i∈s,p i k x):=by convert V.sum s p v h using 1; funext i x; simp
lemma sub{v f g}(h:V.classV v f)(k:V.classV v g):V.classV v (f-g):=by
 rw [sub_eq_add_neg]; apply V.add h; have ht:-g=fun i p => (-1:ℝ) • g i p:=by funext i p; simp
 rw [ht]; exact V.coin _ _ _ k

def mix (a:pLabel G)(b:Ban G): Ban G:= fun i x=>(D₁).weave (stemZero 1 a) (b i x)
lemma single (a:Key G):V.classV (generation a) (castV (stemZero 1 (X a))):=by
 unfold generation; push_cast; rw [vary_X]; exact V.anchor _ _ (high_probe a) -- cast assoc
lemma sprout{I:Type*}(s:Finset I)(v:I→Key G): V.classV (∑i∈s,(generation (v i):ℤ)) (castV (stemZero 1 (∏i∈s,X (v i))))∧ ∀ (p:Ban G)(x:ℤ), Nest T x p →V.classV ((∑i∈s,(generation (v i):ℤ))+x) (mix (∏i∈s,X (v i)) p):=by induction s using Finset.induction_on with
 | empty=>rw [Finset.sum_empty,Finset.prod_empty,_root_.map_one (stemZero 1)]; refine ⟨V.nest _ _ .unit,fun p x h=>?_⟩; rw [zero_add,show mix 1 p=p by funext i z; rw [mix,map_one,Haze.Dose.weave_one]]; exact V.nest _ _ h
 | insert i s hi ih=>
   rw [Finset.sum_insert hi,Finset.prod_insert hi,_root_.map_mul (stemZero 1)]; refine ⟨V.mul (V.single _) ih.1, fun p x h=>?_⟩
   let q: pLabel G:= ∏i∈s,X (v i); let a:=leafProbe 1 (v i)
   have hu: mix (X (v i)*q) p=castV (stemZero 1 (X (v i)))*mix q p+ mix q (crew a p):=by
      funext i x; unfold mix; simp only [Pi.mul_apply,Pi.add_apply,map_mul,vary_X]; rw [Haze.Dose.weave_x]; rfl
   rw [hu,add_assoc]; apply V.add (V.mul (V.single _) (ih.2 p x h))
   rw [add_left_comm]; apply ih.2 _ _; convert skid h a _ (high_probe (v i)) using 1; unfold generation; push_cast; ring
lemma sound {p:pLabel G}(h:IsWeightedHomogeneous generation p n) (q:Ban G)(x:ℤ)(hx:Nest T x q): V.classV n (castV (stemZero 1 p)) ∧ V.classV ((n:ℤ)+x) (mix p q):=by
 classical
 have he (a:Key G→₀ℕ)(ha:a∈ p.support): let P:=monomial a (p.coeff a); V.classV n (castV (stemZero 1 P)) ∧ V.classV ((n:ℤ)+x) (mix P q):=by
   intro f; let I:=(i:↥a.support) × Fin (a i.val); let v:I→Key G:=fun i=>i.1.val
   let Q:= ∏ i:I,(X (v i): pLabel G)
   let c:=p.coeff a
   have hi:f=c • Q:=by rw [show f= _ from (show _ from monomial_eq ..)]; unfold Q; rw [C_mul']; congr 1; unfold Finsupp.prod I v; rw [←Finset.prod_attach,Fintype.prod_sigma]; simp -- attach check
   have ht: n=∑i:I,generation (v i):=Eq.trans (h (mem_support_iff.mp ha)).symm (by rw [Finsupp.weight_apply]; unfold Finsupp.sum I v; rw [Fintype.sum_sigma]; simp [mul_comm]; exact (Finset.sum_attach ..).symm) -- check
   have hr : (n:ℤ)=∑i:I,(generation (v i):ℤ):=by rw [ht,Nat.cast_sum]
   obtain ⟨t,b⟩:=V.sprout Finset.univ v; rw [hi,hr,map_smul]
   refine ⟨V.coin _ _ _ t, ?_⟩
   rw [show mix (c • Q) q=(fun i p=> c • mix Q q i p) from funext fun i=>funext fun z=>by unfold mix; rw [map_smul,Dose.weave_smul]]
   exact V.coin _ _ _ (b _ _ hx)
 let M:=fun a=> monomial a (p.coeff a)
 rw [show castV (stemZero 1 p)=(fun k x=> ∑a∈p.support, castV (stemZero 1 (M a)) k x) from by
     funext k x; change stemZero 1 p=_; conv_lhs=> rw [←p.support_sum_monomial_coeff]
     rw [_root_.map_sum];rfl] -- conv
 refine ⟨V.piles _ _ _ fun i hi=>(he i hi).1,?_⟩
 rw [show mix p q=(fun i x=>∑a∈p.support,mix (M a) q i x) from ?_]; apply V.piles; exact fun i hi=> (he i hi).2
 funext i k; unfold mix Dose.weave
 conv_lhs=> rw [←p.support_sum_monomial_coeff]
 rw [map_sum,map_sum,Finset.sum_mul,map_sum]
end Volume
end YM.SchemeRG11.Long
