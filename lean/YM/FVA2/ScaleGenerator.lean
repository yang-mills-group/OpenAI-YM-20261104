import YM.FVA2.ComposeLog
import YM.FVA2.BetaWay
/-!
# The actual position-scheme generator

MS, X, and Check flows from the same conversion. Strengthen Unity with the ordinary formal
ODE for field frames (B rather than inverse). Homogeneous mass subtraction checked against the
infinitesimal condition, not left implicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.FVA2.RadScale
open Function Filter Topology Set MeasureTheory Finset
open Lattice Maxwell Maxwell.Free Pert Pert.Position Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon Elegant Verne Strat Panel ColorCode
open MS MS.Land MS.Landau MS.Menus MS.Tide MS.Tone Hop Ember Taper Forge
open Month Meter
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{F:Labels.Frames G}
section ops
variable {V:Type*}[AddCommGroup V][Module ℝ V]
lemma substitute (f:Word ℝ)(h:light f)(x:Word V)(n:ℕ): Jet.ren f x n = ∑ j∈ range (n+1), PowerSeries.coeff n (PS f^j) • x j:= by
    let B:= Module.Free.chooseBasis ℝ V; apply B.repr.injective; ext1 i; change B.coord i _= B.coord i _; rw [map_sum]; simp_rw [map_smul]; exact (congr_fun ( ren_writes _ f x ) n ).trans ( Meter.ren_ps f n _ h ) -- name clash order
/-- Directional derivative of precomposition out of the identity g at zero scale shift.
This depends only on strictly previous orders of x if δ starts after tangents (`Month.β`). -/
def incline (β:Word ℝ) (x:Word V)(j:ℕ): V := ∑ i∈ range (j+1),((i:ℝ)*PowerSeries.coeff j ( (PowerSeries.X:SP)^(i-1)*PS β )) • x i
lemma lower_t (β:Word ℝ)(h:β 0=0∧β 1=0)(x:Word V)(j:ℕ): incline β x j=∑ i∈range j, ( ( i:ℝ )*PowerSeries.coeff j ( (PowerSeries.X:SP)^(i-1)*PS β )) • x i:= by
    unfold incline; rw [ Finset.sum_range_succ ]; 
    simp only [PowerSeries.coeff_X_pow_mul',Nat.sub_le,if_true ]; cases j <;> simp [ h, PS ]
end ops
section trig
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
variable (x:Word V) {d:ℕ} (n:ℕ)
-- prove actual derivative and differential β multiplication. Cover naked Powers.$F.Real etc
lemma ren_at {f:ℝ→Word ℝ}{g:Word ℝ}(hf:∀ i, HasDerivAt (fun t=> f t i) (g i) 0)(hz:f 0=headway)(hl:∀ t,light (f t)): HasDerivAt (fun t=>ren (f t) x n) (incline g x n) 0:= by
    unfold incline; simp_rw [ substitute ( f _ ) ( hl _ ) ]; refine HasDerivAt.fun_sum (fun i _=> ?_ );
    simpa only [hz, Meter.head] using! ( Meter.title 0 g f i n hf ).smul_const ( x i )
-- additive buffer exponents f. field generator.B
protected abbrev taps (a b:Buffer F d) := followB a b
abbrev σV (a b:Buffer F d) := RadScale.taps a b
local infixl:70 "⋄"=> σV
lemma zero_lB (a:Buffer F d): 0 ⋄ a=0:= LinearMap.map_zero ( LinearMap.flip (Ribbon.passB (F:=F)) a ) -- check
lemma zero_rB (a:Buffer F d): a ⋄ 0=0:= map_zero ( Ribbon.passB a )
protected lemma affiliation {a b:ℝ→ Buffer F d}{x y:Buffer F d}{k:ℝ}(h:HasDerivAt a x k)(ht:HasDerivAt b y k): HasDerivAt (fun s=> a s ⋄ b s) ( x ⋄ b k + a k ⋄ y ) k:= by
    have he {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](L:E→ₗ[ℝ] E→ₗ[ℝ] E)(a b:ℝ→E)(x y:E)(h:HasDerivAt a x k)(ht:HasDerivAt b y k): HasDerivAt (fun s=> L (a s) (b s)) ( L x (b k) + L (a k) y ) k := by
        let Λ:= L.toContinuousBilinearMap; have he: HasDerivAt (fun s=> Λ (a s)) ( Λ x ) k := Λ.hasFDerivAt.comp_hasDerivAt k h; exact he.clm_apply ht;
    exact he (E:=Buffer F d) (Ribbon.passB (d:=d)) a b x y h ht
-- avoid GLOBAL notation; only in file
local infixl:70 "◆"=> luxury
def crossW (a b:Word (Buffer F d))(n:ℕ): Buffer F d:= ∑ i∈ Finset.range (n+1), a i ⋄ b (n-i)
lemma slotFx (x y:Word (Buffer F d)): (x ◆ y) n=x n+y n+crossW x y n:= by
    apply Subtype.ext; rw [ Erase.reservation ]; unfold crossW;
    simp only [Submodule.coe_add,AddSubmonoidClass.coe_finsetSum ]; rfl
lemma rate {a b:ℝ→Word (Buffer F d)}{x y: Word (Buffer F d)}{s:ℝ}(h:∀ i,HasDerivAt (fun t=>a t i) ( x i ) s) (ht:∀ i, HasDerivAt (fun t=>b t i) ( y i ) s): HasDerivAt (fun t=> ( a t ◆ b t ) n ) ( x n+y n + ( crossW x ( b s ) n+ crossW ( a s ) y n ) ) s:= by
    simp_rw [slotFx ]; unfold crossW; rw [← Finset.sum_add_distrib ]; have H {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{a b:ℝ→V}{x y:V}(f:ℕ→ℝ→V)(g:Word V)(h:HasDerivAt a x s)(ht:HasDerivAt b y s)(hp:∀ i,HasDerivAt (f i) (g i) s): HasDerivAt (fun t=> a t+b t+∑ j∈range (n+1), f j t) (x+y+∑ j∈range (n+1),g j) s:= ((h.add ht).add (HasDerivAt.fun_sum fun i _=> hp i));
    exact H (V:=Buffer F d) _ _ (h n) (ht n) (fun i=> RadScale.affiliation (h i) (ht (n-i)))
end trig
end YM.FVA2.RadScale
namespace YM.FVA2.RadScale
open Function Filter Topology Set MeasureTheory Finset
open Lattice Maxwell Maxwell.Free Pert Pert.Position Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon Elegant Verne Strat Panel ColorCode
open MS MS.Land MS.Landau MS.Menus MS.Tide MS.Tone Hop Ember Taper Forge
open Month Meter
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{F:Labels.Frames G}

namespace Era
open Month (ψ)
abbrev ClockedF (F:Labels.Frames G) := ℝ→Hop F
variable {W:ClockedF F} {A:Panel F}{D:(d:ℕ)→ PositionX.Detector F d}{r:ℝ}{R:PositionX.Bend.Booth r F}(H:Month A W D R)(s:ℝ)(d n:ℕ)
abbrev drive (W:ClockedF F)(D:(d:ℕ)→ PositionX.Detector F d)(t:ℝ)(d:ℕ) : Word (Buffer F d):= (Month.B W D t).wire d
def generation (W:ClockedF F)(D:(d:ℕ)→ PositionX.Detector F d)(d:ℕ) : Word (Buffer F d):= fun i=> deriv (fun t=> drive W D t d i) 0
local notation "Θ"=> drive W D
local notation "b0"=> generation W D
private lemma od_cont {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](f:ℝ→V)(h:ContDiff ℝ ω f): HasDerivAt f (deriv f 0) 0 := (h.differentiable (by simp) 0|>.hasDerivAt)
include H
lemma calendar (n:ℕ): HasDerivAt (fun t=> Θ t d n) (b0 d n) 0:= by exact od_cont (V:=Buffer F d) _ ( H.scales_live d n )
omit H in
lemma honor (W:ClockedF F)(D:(d:ℕ)→ PositionX.Detector F d): drive W D s d 0=0:= Month.warm s W D|>.1 d
lemma first : Θ 0 d=0 := by unfold drive; rw [ H.tentative₀.2, Strat.zeroed ];
-- local CLM issue alias
omit H in
private lemma comp_ge {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V](L:V→ₗ[ℝ] V){t:ℝ}{f:ℝ→V}{v:V}(h:HasDerivAt f v t): HasDerivAt (fun s=> L ( f s )) ( L v ) t:= L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h
omit H in
private lemma ford {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{v:V}{f:ℝ→V} {t:ℝ}(h:HasDerivAt (fun s=> f (s+t)) v 0): HasDerivAt f v t:= by
   obtain ht: HasDerivAt (fun x=> f (x+t)) v (t-t):= by simpa using h;
   rw [show f=(fun s=> f (s+t)) ∘ (fun x=> x-t) from funext fun x=>( by simp )]; simpa using! ht.scomp (h:=fun x=> x-t) t (( hasDerivAt_id t ).sub_const t )
omit H in 
lemma foundation (W:ClockedF F)(D:(d:ℕ)→ PositionX.Detector F d) : generation W D d 0=0 := by unfold generation; simp_rw [honor ..]; exact deriv_const (x:=(0:ℝ)) ( c:=(0:Buffer F d) )
local infixl:70 "◆"=> luxury
lemma standard : HasDerivAt (fun t=> Θ t d n) (( Taper.Step s ) ( b0 d n ) + incline ( Month.β W ) ( Θ s d ) n + crossW ( Taper.Step s ∘ b0 d ) ( Θ s d ) n ) s:= by
    -- use group law with the differentiated argument first
    apply ford (V:=Buffer F d)
    have hv (i:ℝ): Θ (i+s) d= (Taper.Step s ∘ Θ i d ) ◆ ren ( Month.ψ W i ) ( Θ s d ) := by
       unfold drive; rw [ ( Month.stages H i s ).2, Strat.pay _ _ d, Taper.reflectStep s, Strat.resume_wire ];-- 
    simp_rw [hv];
    let P:= Taper.Step ( F:=F ) ( d:=d ) s; let f(t):= P ∘ Θ t d; let g(t):= ren (ψ W t) (Θ s d);
    let δ := incline ( Month.β W ) (Θ s d);-- uses n?”
    have hp : HasDerivAt (fun t=> (f t◆ g t) n) ( P (b0 d n)+ δ n+( crossW ( P ∘ b0 d ) (g 0) n+ crossW ( f 0 ) δ n )) 0 := rate n ( x:=P ∘ b0 d ) ( a:=f ) ( b:=g ) ( fun i=> by exact comp_ge (V:=Buffer F d) P (calendar H d i) ) ( fun i=>by exact ren_at (V:=Buffer F d) _ i H.headB H.tentative₀.1 (fun s=>(W s).rooted) );
    have hf : g 0=Θ s d:=by unfold g; rw [ H.tentative₀.1,ren_head (V:=Buffer F d) ];
    have hg : f 0=0:=by unfold f; rw [ first H ]; exact funext fun i=>map_zero P
    rw [hf,hg, show crossW ( 0:Word (Buffer F d) ) δ n=0 from (by simp only [crossW,Pi.zero_apply,zero_lB,Finset.sum_const_zero]),add_zero ] at hp;
    exact hp

/-- The b-flow from Month meets the manuscript grading criterion. -/
def Preserves (W:ClockedF F)(D:(d:ℕ)→ PositionX.Detector F d): Prop:= ∀ d n,Verne.withinBlock F (generation W D d n)=generation W D d n
-- equivalent to property of the actual frame families.No compatibility of generator across unrelated transports.
def FinalB (W:ClockedF F)(D:(d:ℕ)→ PositionX.Detector F d): Prop:= ∀ s, Strat.only (Month.B W D s)=Month.B W D s
omit H in
private lemma equ_steady {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{f g:ℝ→V}{u:ℝ→V}(h:∀ s, HasDerivAt f (u s) s)(hx:∀ s, HasDerivAt g (u s) s)(h0:f 0=g 0): f=g:= by
   let δ:= f-g; have hh: ∀ t:ℝ,HasDerivAt δ 0 t:= fun t=> by simpa using! (h t).sub ( hx t )
   funext t; have he:= is_const_of_deriv_eq_zero (𝕜:=ℝ) (f:=δ) (fun t=> (hh t).differentiableAt) (fun t=> (hh t).deriv) t 0; exact sub_eq_zero.mp (he.trans (sub_eq_zero.mpr h0)) -- parenthesis
local infixl:70 "⋄"=> σV
lemma only_v (hf:Preserves W D)(s:ℝ) : withinBlock F (Θ s d n)=Θ s d n:= by
    let L:= Verne.withinBlock F (d:=d); induction n using Nat.strong_induction_on generalizing s with| h n ih=>
     have hx(t:ℝ): let f:= Θ t d; let δ:= Taper.Step t ∘ b0 d; L (δ n + incline ( Month.β W ) f n + crossW δ f n)=δ n+incline ( Month.β W ) f n + crossW δ f n:= by
          intro f δ; have he: Taper.Step t ∘ b0 d=b0 d:= funext fun i=> Taper.solar _ _ (hf d i); change L ( (Taper.Step t ∘ b0 d) n+_+crossW ( Taper.Step t ∘ b0 d ) f n )=(Taper.Step t ∘ b0 d) n+_+crossW ( Taper.Step t ∘ b0 d ) f n; -- check
          rw [ he,map_add,map_add, lower_t _ H.zeroβ,show L ( b0 d n)=_ from hf d n ]; unfold crossW; rw [ map_sum,map_sum ]; refine congr_arg₂ (·+·) ( congr_arg (_+·) ?_ ) (Finset.sum_congr rfl ?_); · simp_rw [map_smul]; apply Finset.sum_congr rfl; intro i hi; rw [show L (f i)=_ from ih i (Finset.mem_range.mp hi) t ];
          intro i hi; by_cases hp:i=0; · subst i; rw [foundation,zero_lB,map_zero ];
          have hv:= Finset.mem_range.mp hi; rw [show L (RadScale.σV _ _)= RadScale.σV (L (b0 d i)) (L (f (n-i))) from Verne.hom ..,show L ( b0 d i )=_ from hf .., show L (f (n-i))=_ from ih (n-i) ( by omega ) t ]; -- ω for n=0 case uses i≤n?
     let q(t:ℝ):= Θ t d n;
     refine congr_fun (equ_steady (V:=Buffer F d) (f:=fun t:ℝ=>L (Θ t d n)) ?_ (g:=q) (fun t=> standard H t d n) ?_) s
     · intro i; obtain hT := comp_ge (V:= Buffer F d) L (standard H i d n); change HasDerivAt _ (Taper.Step i (b0 d n)+_+_) i; exact (hx i) ▸ (show HasDerivAt (fun s:ℝ=> L (Θ s d n)) (L (( Taper.Step i ∘ b0 d ) n+_+_)) i from hT)
     unfold q; rw [ first H ]; exact map_zero _
-- compatible through increasing horizons via only property.Converse.
omit H in
private lemma uniqD {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{f:ℝ→V}{x y:V}{t:ℝ}(h:HasDerivAt f x t)(hv:HasDerivAt f y t): x=y:= h.unique hv
lemma equivalent : FinalB W D ↔ Preserves W D:= by
    constructor
    · intro h d n; have he:= calendar H d n; have hp(t:ℝ): withinBlock F (Θ t d n)=Θ t d n:= congr_fun ( congr_arg (fun p:Strat F=> p.wire d) (h t)) n; apply uniqD (V:=Buffer F d) _ he;
      have hx:= comp_ge (V:=Buffer F d) (withinBlock F) he; simp_rw [hp] at hx; exact hx
    intro h t; exact Strat.ext fun d=> funext fun n=> only_v H d n h t

omit H in
lemma graded_equ (W:ClockedF F)(D:(d:ℕ)→ PositionX.Detector F d) (s:ℝ): (W s).gradedStep ↔ (Month.B W D s).only=(Month.B W D s):= by
    obtain ⟨hp,hx,hq,hh⟩:=Month.warm s W D;
    constructor; · intro h; rw [show only ( W s ).Z= _ from h] at hx; calc
                             _ = only (Month.B W D s)*1:= (mul_one _).symm
                             _ = _:=by rw [ ← hh,←mul_assoc,hx,one_mul ];
    intro h; unfold gradedStep; rw [h] at hx; calc
                      _ = 1*only (W s).Z:=( one_mul _ ).symm
                      _ = _:=by rw [←hh,mul_assoc,hx,mul_one ]
lemma gradingCriterion : Preserves W D ↔ ∀ s,(W s).gradedStep:= by rw [ ← equivalent H ]; exact forall_congr' fun i=>(graded_equ W D i).symm
end Era
end YM.FVA2.RadScale

