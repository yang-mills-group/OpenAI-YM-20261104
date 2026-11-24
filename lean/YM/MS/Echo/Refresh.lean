import YM.MS.Echo.Clear
/-!
# Exact UV Ward transport. Linear flow on prim and central pairwise differences. Only meeting
at stencil differences through orders ≤n at some y. Nothing asserted about residual harmonic mode.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Echo
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Native
open Lattice Book Convolve Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Flux City Signal Modeled Frame
open scoped Topology ContDiff Interval
variable {G:Gauge}{n i k:ℕ}{ φ H J: Actor G}{u v w:ℤ}{X F U V:Dec G}{p:Team}
local notation "B"=> Spectrum G
variable (x:ℝ)(h:PC G p X)(hp:PM φ X F u)
local notation "S"=>res X F x
local notation "ξ"=> Ω G
include h hp
lemma initialT (hm: Circle G φ false u)(i:ℕ): S 0 i= run (steadyE B (style G p x) (φ x) i):= by
   let S0:= res X F x; let Q : ℝ→ T (Law G):= payR X x; let U := φ x; let K:=style G p x; let Z:= promote run U; let D:= promote run K; have hy j : payR F x 0 j=Z j:=(hp.recu ..).1; have ht j (hh:1 ≤ j): Q 0 j=D j:=(h.recu j hh x).1
   let C:=(ξ 0).C; have hh : pairW C (Q 0) (payR F x 0) i= ∑ j∈Domain.paths i 0,C (D (i-j)) (Z j):= by rw [ paired, canon_sub (fun i j=> C (Q 0 i) (payR F x 0 j)),show Q 0 0=0 from centered h x 0,map_zero,LinearMap.zero_apply,zero_add ]; exact Finset.sum_congr rfl (fun j hj=> by rw [hy,ht _ (by obtain hx:=path_in hj; omega)])
   obtain ht:= period0 μzone cour0 (mood_f G) (t:=0) ((hp.owes i).stay x).joint; change Pass (Mood G 0) (payR F x 0 i) μzone at ht; rw [hy] at ht;
   ext l; unfold res GridR.res; rw [ Pi.add_apply, show pairW _ _ _ i=_ from hh, promised,hy ]; simp only [C,Ω,rack,LinearMap.add_apply,Pi.add_apply,Finset.sum_apply,blvd ]; rw [ finite_cc μzone ht ]; simp_rw [show Mood G 0=Kzone G from funext fun i=>funext fun j=>funext (born_int i j) ];
   change (send wave).raise (run (φ x i)) l + cycle (Kzone G) μzone (run ( φ x i )) l + (∑ j∈ Domain.paths i 0, tree parity (Kzone G) ( D (i-j) ) ( Z j ) l )= run ((B).Lap ( φ x i )+ (∑ j∈ antidiagonal i,(B).touch ( K j.1 ) ( U j.2 ))) l; simp_rw [map_add,map_sum, Pi.add_apply,Finset.sum_apply, Tone.touching ]; -- lens
   rw [ lapC ( φ x i ) ( hm.actual i x |>.symm ), canon_sub (fun k j=> tree parity ( Kzone G ) ( run (K k)) ( run (U j)) l), show K 0=_ from whoZero p x (core G), show tree parity (Kzone G) (run (core G 0)) (run (U i))=(send wave).raise (run (φ x i)) from Vin ( run ( U i )) (tied.sym _ ( hm.actual i x|>.symm ))]; abel -- names
lemma lively (H':G.Simple)(k:ℕ)(t:ℝ): Zip (fun t=>S t k) ((ξ t).lives (payR X x t) ( S t ) k) t := by
    obtain hx := mark_field x h hp k t; rw [ show pairW _ _ _ k= ( 0: Law G ) from ?_,add_zero ] at hx; exact hx
    -- may implicit h missing
    rw [ paired ]; apply Finset.sum_eq_zero; intro i _; change tree _ _ _ _ = ( 0:Law G ); rw [ tree_agrees _ _ _ _ _ ( realized x H' h i.1 t ) ]; change (ξ t).X (0:Law G) _=0; rw [map_zero,LinearMap.zero_apply]
lemma survive (H':G.Simple) (hx:Circle G φ false u) (hm:PM H X U v) (he:PM J X V w)(k:ℕ)(hs:similar ( steadyE B ( style G p x ) ( φ x ) ) (H x - J x) k) : ∀ t, S t k=(U k x - V k x) t:= by
    induction k using Nat.strong_induction_on with| h k ih=>
       let Y:= fun t:ℝ=> S t k; let F0:= U k x; let F1:= V k x; let F' := F0-F1; let C:= Y-F'; obtain ht:= total_slot x h hp.owes k 1; simp_rw [one_smul] at ht; obtain ⟨hz,r,hr⟩:= (show TouchF Y∧∃ r,Rank Y r from ht); obtain ⟨u,hU⟩:= hm.owes k|>.pay; obtain ⟨v,hV⟩:= he.owes k|>.pay;
       have hvM: Wind.Near false C:= by
           refine ⟨ ?_,?_,?df⟩; · exact Vista.look_sub.Tneg hz (Vista.look_sub.Tneg (( hm.owes k ).stay x|>.joint) (( he.owes k ).stay x|>.joint))
           · refine ⟨ max r ( ↑(u+v) ), Rank.sub ( hr.pay (le_max_left ..)) (Rank.sub ?_ ?_) ⟩ <;> first|exact (hU x).pay (by omega)|exact (hV x).pay (by omega)
           intro t l _; let D:=payR X x t; let P:=(ξ t).lives D; let L':=(ξ t).L
           have hs' : P (S t) k- (P (payR U x t) k-P (payR V x t) k) = Wiref G C t:= by
               have ht j (hj:j<k): S t j=U j x t-V j x t:= ih j hj (fun i hi=> hs i ( hi.trans hj.le )) t; unfold P GridR.lives; simp only [ Pi.add_apply, promised ]; -- compare worries point not at l.
               have hv : ∀ W:T (Law G), pairW (ξ t).X D W k=∑ i∈Domain.paths k 0, (ξ t).X (D (k-i)) (W i):= by intro W; rw [paired,canon_sub (fun i j=>(ξ t).X (D i) (W j)), show D 0=0 from centered h _ _,map_zero,LinearMap.zero_apply,zero_add]
               rw [ hv,hv,hv ]; have hm0:(∑ i∈Domain.paths k 0,(ξ t).X (D (k-i)) ( S t i))=((∑ i∈Domain.paths k 0,(ξ t).X (D (k-i)) ( U i x t ))-∑ i∈Domain.paths k 0,(ξ t).X (D (k-i)) ( V i x t )):= by rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [ht i (path_in hi|>.2), map_sub]
               rw [ hm0 ]; unfold C F'; simp_rw [ map_sub,Pi.sub_apply ]; dsimp only [payR,F0,F1,Y]; abel -- target Grid linear.LV
           obtain hh := ( lively x h hp H' k t l ).sub (( priorM h hm x t k l ).sub ( priorM h he x t k l )); convert! hh using 1; exact ( congr_fun hs' l ).symm
       have hT : C=0 := Dtotal hvM (by
           change S 0 k - ( F0 0 - F1 0 )=0; rw [initialT x h hp hx,hs k k.le_refl, Pi.sub_apply, map_sub, show F0 0=_ from ( hm.recu k x ).1, show F1 0=_ from ( he.recu k x ).1, sub_self ])
       exact congr_fun (sub_eq_zero.mp hT)
end YM.MS.Echo
