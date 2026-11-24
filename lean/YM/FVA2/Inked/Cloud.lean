import YM.FVA2.Inked.Synth
import YM.FVA2.Gen.RealJ
/-!
 # Full classical formula → seeded symbol. At any finite rank, evaluated at z(coupling)=1.
    Handles all ghost directions at base mark. Curvature formula proven as jets.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked
open Function Filter Set Finset MeasureTheory Topology
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
local notation "W"=> G.Color
local notation "K"=> Cfield G 0
local notation "│"=> basis
variable {A:Play E G}{Z:E→ Sky G}{x:P}{a b:Axis}{i:G.ColorIndex}{k j:ℤ}
structure High (A:Play E G) (F:E× P→ G.Color)(k:ℤ)(V:Mield G 0): Prop where
    smooth : ContDiff ℝ ω F
    earns (i:G.ColorIndex): Hero A k (laser i ∘ F) (V i)
namespace High
variable {F H:E × E4→ G.Color}{B C : Mield G 0}
lemma gift (h:High A F k B): High A (par ((0:E),basis a) F) (k+1) ( axisP a B ):= by
    refine ⟨ mixed_par h.smooth, fun i=>?_⟩; obtain he : ContDiff ℝ ω (laser i ∘ F):= (h.earns i).smooth; refine ( show Hero A (k+1) (laser i ∘ par _ F) _ from ?_ ); rw [ show (laser i ∘ par ((0:E),basis a) F)= ( fun p:T=> par (basis a) (fun t:P=> (laser i ∘ F) (p.1,t) ) p.2 ) from ?_ ]; swap; · funext p; exact ( ( layerR he (basis a) p ).symm.trans ( par_L (laser i) (h.smooth.differentiable (by simp) p) ) ).symm -- flipped
    exact (h.earns i).parL
lemma dif (h:High A F k B) : High A ( fun x:E×P=> par (basis a) (fun t:P=> F (x.1,t)) x.2 ) (k+1) (axisP a B):= by rw [show (fun x:T=> par (basis a) (fun t:P=> F (x.1,t)) x.2 )=par ((0:E),basis a) F from funext fun p=>( layerR h.smooth _ p ).symm ]; exact h.gift
lemma colorM (h:High A F k B)(ht:High A H j C): High A (fun x=> G.ad ( F x ) ( H x )) (k+j) ( jaw G 0 B C ) := by
    refine ⟨?_,fun i=>?_⟩; · let K':W→L[ℝ]W→L[ℝ]W:= LinearMap.toContinuousLinearMap ( LinearMap.toContinuousLinearMap.toLinearMap.comp G.ad ); exact ( ( K'.contDiff.comp h.smooth ).clm_apply ht.smooth )
    rw [chew,show (laser i ∘ _)=(∑ d:G.ColorIndex, ∑ c:G.ColorIndex, ( letterLie d c i ) • ((laser d ∘ F)*(laser c ∘ H))) from ?_ ]; swap; · funext x; simp_rw [ Finset.sum_apply ]; exact taste ..
    exact Hero.sum _ (fun x _=> Hero.sum _ (fun y _=> ((h.earns x).times (ht.earns y)).smul (letterLie x y i) ))
lemma zero (k:ℤ): High A ( fun _:T=> (0:W) ) k 0:= ⟨contDiff_const,fun i=> by rw [ show laser i∘ _= (0:T→ℝ) from funext fun _=> map_zero _ ]; exact Hero.zero k ⟩
lemma smul (c:ℝ)(h:High A F k B): High A (c • F) k (c • B):= by
    refine ⟨ h.smooth.const_smul c, fun i=>?_⟩; rw [ show laser i ∘ (c • F) =c • ( laser i ∘ F ) from funext fun _=> map_smul (laser i) c (F _) ]; exact (h.earns i).smul c
lemma add (h: High A F k B)(ht: High A H k C): High A (F+H) k (B+C):= by refine ⟨ h.smooth.add ht.smooth, fun i=>?_⟩; rw [ show laser i ∘ (F+H)=( laser i ∘ F ) + laser i∘H from funext fun _=> map_add .. ]; exact (h.earns i).add (ht.earns i)
lemma sub (h:High A F k B)(ht:High A H k C): High A (F-H) k (B-C):= by simpa only [neg_one_smul,sub_eq_add_neg] using h.add ( ht.smul (-1) )
lemma sums {S:J→ E × P→W}{X:J→ Mield G 0}(s:Finset J)(h:∀ i∈s, High A (S i) k ( X i )): High A ( ∑ i∈s, S i ) k ( ∑ i∈s, X i ) := by induction s using Finset.induction_on with | empty=> simp_rw [sum_empty]; exact zero k| insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add ( ih fun i hi=> h i (mem_insert_of_mem hi) )
end High
variable {F:E→ Mist G}{B:Mield G 0}(h:Hall A Z)
include h
lemma crest (i:Axis): High A (fun x:E×P=> Z x.1 i x.2) 1 (Motif.A 0 G i) := ⟨ h.speaks i,h.aura i ⟩
lemma colorD (a:Axis)(hx:High A (fun x:E×P=> F x.1 x.2) k B): High A (fun x:E×P=> deriveN ( Z x.1 ) ( F x.1 ) a x.2 ) (k+1) ( convoke 1 a B ) := by rw [convoke,one_smul,LinearMap.add_apply]; obtain he:=(crest h a).colorM hx; rw [ add_comm (1:ℤ) ] at he; exact hx.dif.add he
lemma pureF (i j:Axis): High A (fun x:E×P=> surf ( Z x.1 ) i j x.2 ) 2 (cur (G:=G) (n:=0) 1 i j) := by
    rw [cur,one_smul,F₀,show ∀ (x y z:Mield G 0), x-y+z=(x+z)-y from fun _ _ _=>by abel]; apply High.sub ( ht:= (crest h i).dif ) (h:=?_); exact ( (crest h j).dif ).add ((crest h i).colorM (crest h j) )
lemma refract (n:ℕ): High A (fun z:E×P=> gleam (Z z.1) x a b n z.2 ) (n+2:ℤ) ( graft 1 a b x n ):=by
    induction n with| zero=> rw [ Nat.cast_zero,zero_add ]; exact pureF h ..| succ k ih=>
       push_cast; rw [ add_right_comm (k:ℤ) 1 2,graft,show (fun z:E×P=> _)=∑ i:Axis,x i • (fun z:E×P=> deriveN (Z z.1) (gleam ( Z z.1 ) x a b k) i z.2 ) from funext (?_ : ∀ z:E×P,_=_) ]; swap; · intro z; rw [gleam]; simp only [ Finset.sum_apply, Pi.smul_apply ]
       exact High.sums _ (fun i _=> ( colorD ( F:=fun z:E=> gleam ( Z z ) x a b k ) h i ih).smul (x i) )
private def scoreRay (n:ℕ)(p:Sky G)(y:E4)(x:E4)(a:Axis): W:= (slotDen n)⁻¹ • ( ∑ j:Axis,x j • gleam p x j a n y )
private lemma sphere (n:ℕ): High A (fun z:E×P=> scoreRay n (Z z.1) z.2 x a) (n+2:ℤ) ( Ray G 0 n 1 a x ):= by
    rw [Ray,show (fun z:E×P=> _)=(slotDen n)⁻¹ • (∑ i:Axis,x i • (fun z:E×P=> gleam (Z z.1) x i a n z.2)) from ?_ ]; · exact ( High.sums _ (fun i _=> ( refract h n ).smul (x i)) ).smul _
    funext z; simp only [scoreRay,Pi.smul_apply,Finset.sum_apply ]
omit h
-- remove nonzero x and test shape afterwards.Symbol-level
structure Early (A:Play E G) (f:E→ℝ)(k:ℤ)(B:Law G): Prop where
    smooth : ContDiff ℝ ω f
    cap : Limit B k
    starts (w:Legs (Lane4 G))(hw:Active A w): I^(k-(w.length:ℤ)) * ink A.shots f w = B w
private lemma pr_early {F:E×P→ℝ}{B: Law G}(h: Hero A k F B): Early A (fun x:E=> F (x,0)) k B:= ⟨ h.smooth.comp (f:=fun x:E=>(x,(0:P))) (contDiff_id.prodMk contDiff_const),h.caps, fun w hw=> by simpa only [ flight_at,Complex.ofReal_one,one_mul ] using h.starts 0 w hw ⟩
variable {R:E→ Labels.Jet G} (hm: ∀ x:E, Radials (Z x) (R x) )(n:ℕ)
local notation "ℵ"=> asC G n
include h hm
lemma sky_early (c:Coord G n): Early A (fun x:E=> c ( R x n )) (n+2:ℤ) (Ramp G n (ℵ c) 1 0):= by
    refine Submodule.span_induction (p:=fun (X:Coord G n) _=> Early A ( fun x:E=> X ( R x n ) ) (n+2:ℤ) ( Ramp G n (ℵ X) 1 0 )) ?_ ?_ ?_ ?_ (show c∈ Submodule.span ℝ (Samples G n) from by rw [many]; exact Submodule.mem_top)
    · rintro _ ⟨a,x,v,rfl⟩; rw [ramp_Jrad, show (fun y:E=> Prong a x v ( R y n ))= ( fun y:E=> ( laser v ) ( scoreRay n ( Z y ) 0 x a ) ) from ?_ ]; · exact pr_early ( ( sphere (a:=a) (x:=x) h n ).earns v )
      funext y; change ( R y n ).value a x v= _; rw [ hm y ]; rfl -- slotDen
    · simp_rw [map_zero]; refine ⟨ contDiff_const,(fun _ _=> rfl), fun w hw=>?_⟩; change I^_*ink _ (0:E→ℝ) w=_; rw [ink_zero]; simp
    · intro a b u v he hv; rw [map_add,map_add,Pi.add_apply,Pi.add_apply]; refine ⟨ he.smooth.add hv.smooth,he.cap.add hv.cap, fun w hw=>?_ ⟩; change I^_*ink _ ((fun x:E=> a ( R x n ))+(fun x:E=> b ( R x n ))) w=_; rw [ink_add _ he.smooth.contDiffAt hv.smooth.contDiffAt,Pi.add_apply,Pi.add_apply,mul_add,he.starts w hw,hv.starts w hw]
    intro a v u he; rw [map_smul,show a • (ℵ v)=(a:ℂ) • ℵ v from rfl,map_smul,Pi.smul_apply,Pi.smul_apply]; refine ⟨ he.smooth.const_smul a, he.cap.smul _, fun w hw=>?_⟩; change I^_*ink _ (a • (fun x:E=>v ( R x n ))) w=_; rw [ink_smul _ he.smooth.contDiffAt, Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,mul_left_comm _ (a:ℂ),he.starts w hw]
end YM.FVA2.Inked
