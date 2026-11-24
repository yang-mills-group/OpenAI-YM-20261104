import YM.FVA2.TreeT.Stamp
/-!
 # All-times LPT tree-width highest-rank flow. For all geometry fields.
 Need certify nonlinear **initial stencil** condition (NOT assumed for callers of final comparison).
 Use unmarked only on-net for this stage. Lattice kernel here. -/
noncomputable section
set_option maxRecDepth 4200
set_option maxHeartbeats 500000
set_option autoImplicit false
namespace YM.FVA2.TreeT.Pulse
open Function Filter Set Finset MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Heat MS.Plane.Flux MS.Landau MS.Landau.Detect MS.High MS.Arts
open MS.City MS.Plane.Wire MS.Wind MS.Wind.Modeled MS.Tone MS.Momentum MS.Tone.Frame Lattice
open MS.Native MS.Native.Wilsonian MS.Menus MS.Local.Physical MS.Outlook MS.Emit MS.Land
open MS.Pearl MS.Garment.Wick MS.Plane.Domain MS.Lifting
open MS.Book MS.Book.Program MS.Book.Convolve MS.High.Knobs MS.Color MS.Wind.Leading MS.Heat.Signal
open Teller Graft Capacity
open scoped Topology ContDiff Interval Classical
variable {G:Gauge}{n d k r:ℕ}{b:Bool}{F H: MS.Wind.Flow G}{A:Law G}{t y x:ℝ}{w:List (Lane4 G)} {p:Team}
lemma ascent (h:G.Simple)(p:Team) (x y:ℝ): Graft.Above true wfield 4 (n+2) ( skyline G p n x y ):= by
    rcases n with _|(_|n); · rw [skyPC .. |>.free]; exact fun w h h' => Before.zero _
    all_goals intro w h' hw; refine ⟨((skyPC G p |>.owes _ ).stay x|>.joint).routine _ _, ?_⟩; intro i hi
    swap; exact False.elim (by have h:= length_pay w; omega)
    change torch _ _ _=0; rw [torch_piece _ hw]; change torch i (Book.mask 3 ( skyline G p 1 x y )) w=0; rw [show Book.mask _ _= Menus.Top G from (Wind.first_top (skyPC G p) x|>.2 y), Lifting.face_here ( Menus.bulk_three h ) ( w:=w ) h' i (by omega), if_neg (by omega)]
lemma zero_width (G:Gauge)(x:ℝ)(i j:BH G)(hu:3<wfield i+wfield j): Cpu G x i j = 0:= by
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,c⟩ <;> norm_num [Landau.wfield,Landau.dim] at hu; all_goals funext p; all_goals simp [Cpu,LegsK,Landau.choir,City.L0]
-- differ from Log.Part uses on all native points, at real R (not log)
lemma drives (h: ∀ t, Zip F (H t) t) (he:TouchF F) (hw:TouchF H)(w:List (Lane4 G))(j:ℕ) (t:ℝ) : HasDerivAt (fun s=> torch j (F s) w) (torch j (H t) w) t:= by
    let v:= ray w; let Q : ℝ×ℝ→ℂ := fun p=> H p.1 (sail v p.2); have hQ: ContDiff ℝ ∞ Q:= jointWay hw v
    have hv (t:ℝ): fieldVal (F t) v= fieldVal (F 0) v+ fun x:ℝ=> desk Q (t,x):= by nth_rw 1 [term_account he hw h]; rfl
    let L(p:ℝ):= iteratedFDeriv ℝ j ( fieldVal ( F p ) v ) 0; let V:= ContinuousMultilinearMap.apply ℝ (fun i:Fin j=>ℝ) ℂ (fun _=>1); let K : ℝ → ℂ:=fieldVal (F 0) v; have hX(t:ℝ):ContDiff ℝ ∞ (fun x:ℝ=> desk Q (t,x)):= (park hQ).comp (show ContDiff ℝ ∞ (fun x:ℝ=>(t,x)) by fun_prop)
    have H' : HasDerivAt L (iteratedFDeriv ℝ j (fieldVal ( H t ) v ) 0 ) t:= by
       let Θ(s:ℝ) := iteratedFDeriv ℝ j (fun p:ℝ=>desk Q (s,p)) 0; have hZ(s:ℝ) : L s= iteratedFDeriv ℝ j K 0 + Θ s :=by unfold L; rw [hv, iteratedFDeriv_add ((show ContDiff ℝ ∞ (fieldVal ( F 0 ) v) from he.routine v 0 ).of_le (by exact_mod_cast le_top)) ((hX _).of_le (by exact_mod_cast le_top)),Pi.add_apply]
       rw [funext hZ]; exact ( deskD_iter hQ j t 0 ).const_add (iteratedFDeriv ℝ j K 0)
    convert! ( ( (j.factorial:ℝ)⁻¹ • V ).hasFDerivAt.comp_hasDerivAt t H' ) using 1 -- implicit.V.
private lemma bill0 {U : ℝ→Flux (BH G) QP ℂ}(h:flex U) (t:ℝ)(i j:BH G): ContDiff ℝ ∞ (U t i j):= (h i j).comp (f:=fun p:QP=>(t,p)) (by fun_prop)
lemma awaiting {U:Dec G}{φ:Actor G} (_hm:PM φ ( skyline G p ) U 0) (h:G.Simple) (ht:∀ i t, Rank ( U i t ) (r+(i:ℤ))) (x t:ℝ) (hv:∀ i<n,∀ y:ℝ, Graft.Above false wfield d (r+i) (U i x y)) : Graft.Above false wfield ( (d:ℤ)+1 ) (r+n) ( path 1 n 0 (skyline G p) U x t):= by
    intro w hx hW; rw [quarterback]; simp only [Complex.ofReal_one,one_smul ]; unfold fieldVal; simp_rw [Finset.sum_apply]; refine Before.transit _ (fun i hi=>?_); obtain ha:= (path_in hi).2
    have he(i j:BH G):= bill0 ( U:=Cpu G ) (City.main_f G) t i j
    obtain hL:= Graft.joint_wire (ascent (n:=n-i) h p x t) (hv i ha t) ( Vrev G t ) (show Limit _ ( ↑(n-i+2):ℤ ) from Limit.up (Lambda.Finite.ranked ( skyPC G p ) (n-i) x t) (by omega)) (show Limit _ (↑(r+i):ℤ) from Limit.up ( ht i x t ) (by omega)) (zero_width G t) he (r:=r+n) (by omega); rw [show ( d:ℤ )+1=4+d-3 from ( by omega )]; exact hL w hx hW
-- closed. no pole comparisons in this lemma (only on L lattice).
lemma shield {U:Dec G}{φ:Actor G} (hm:PM φ ( skyline G p ) U 0) (h:G.Simple) (ht:∀ i t, Rank ( U i t ) (r+(i:ℤ))) (X:ℝ) (hX:∀ i, Graft.Above false wfield d (r+i) (run ( φ X i ))) (n:ℕ) : (∀ y:ℝ,w.length=r+n→fieldDim wfield w+k≤d→ torch k ( U n X y ) w= torch k (run (φ X n)) w) ∧∀ y:ℝ, Graft.Above false wfield d (r+n) (U n X y) := by
    induction n using Nat.strong_induction_on generalizing w with
    | _ n ih=>
       let L:= U n X; let W:= path 1 n 0 (skyline G p) U X; let T:= Wiref G L+W; have hmL:= (hm.owes n|>.stay X).joint; have ht0:= path_c 1 n 0 (skyline G p) U (fun i _=> skyPC G p|>.owes _) (fun i _=> hm.owes _);
       obtain hs:= hm.recu n X; have hn :∀ t, Zip L ( T t ) t:= hs.2; have hb (j:ℕ) (w:List (Lane4 G))(hV:w.length=r+n): (fieldDim wfield w)+(j:ℤ)≤d → ∀ y:ℝ, torch j (U n X y) w= torch j (run (φ X n)) w:= by
          intro hh y; refine Eq.trans ( constancy (f:=fun y:ℝ=>torch j (U n X y) w) (fun t=>?_) y ) (congr_arg (fun F=>torch j F w) hs.1); obtain hp:= drives (H:= T) hn hmL ( ( lapid_touch hmL (main_f G)).add (( ht0.stay X ).joint) ) w j t; convert hp using 1; apply Eq.symm; 
          have hH: fieldVal ( T t ) (ray w)=fieldVal ( W t ) (ray w):= by
             funext x; unfold fieldVal T; simp only [Pi.add_apply]; rw [ ( show lapidus (Cpu G) ( L ) t _=0 from lapid_max hmL (main_f G) ( ht n X ) t ( sail ( ray w ) x ) (by simp only [sail_len,ray_len]; omega)),zero_add] -- test
          unfold torch; rw [hH]; exact ( awaiting (d:=d) hm h ht X t (fun i hi=> ( ih i hi ( w:=w ) ).2 ) w (fun t=> Bool.noConfusion t) hV ).start j (by omega)
       refine ⟨ fun y h=>fun hp=> hb k w h hp y , fun t w hw hL=> ⟨ hmL.routine _ _,fun i hi=>?_ ⟩⟩; exact ( hb i w hL (by omega) t ).trans ( ( hX n w hw hL ).start i hi )
end YM.FVA2.TreeT.Pulse
