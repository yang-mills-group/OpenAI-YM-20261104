import YM.MS.Vista.Clock
/-!
# Geometry.API Meets across rooted directions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E:Type}{L:I→Side}{P:Belt I}{ V:Visa I}{X:Rake.Site G I}{Z:Lin I}{K: Planet G I}
    {F H:Glade G I}{ Q:ℕ→I→Law G}{b c: Bool}{A B:Faces I}{u v x:P.time→ℝ}{ν:P.time→Measure QP}
structure TPaid (P:Belt I)(ν:P.time→Measure QP)(v:P.time→ℝ)(A B:I→Cover): Prop where
    length (i:P.time): P.price.length i ≤ v i
    remote(b:Bool) : Radar P.price v ( Ap P (env b A B) ) ν
    cost : Mileage P.price (Ap P ( A-B )) v
lemma adjustL (a:P.time→ℝ)(hp:nn a)(hv:HandC b c P F a): HandC b c P (adjust Z.orbit F) a:= by
   cases hZ: Z.orbit; · rw [adjust,if_neg (by decide :¬false=true)]; unfold HandC; rw [map_zero]; exact Lease.zero hp
   rw [adjust,if_pos rfl]; exact hv
lemma G_nn (S:Scale I)(v u:I→ℝ)(h:nn u)(hP:nn v)(l:ℕ): nn (Growth S v u l):=fun i=> mul_nonneg ( h i ) ( pow_nonneg ( div_nonneg ( S.pos i |>.le ) (hP i) ) _ )
variable {s:P.time→ℝ}
lemma cabin_T (H1:Vel P Z K ν x)(hc:TPaid P ν s A B)(hp:WarpHere false true P F u)(hx:WarpHere false true P H v)(he:Toned F)(hf:Toned H)(hP:nn u)(hh:nn v)(i:ℕ): HandC false false P ( zip2 Z K A B F H ) (Growth P.price s (x*u*v) i):= by
   let V(b:Bool):= BookOn H1 s ( hc.remote b ) hc.cost hc.length hp hx he hf hP hh i; apply beauty ( V false ) ( adjustL _ _ ( V true )); exact G_nn _ _ _ ( joy (joy H1.2.2 hP) hh ) ( fun i=> ( P.price.pos i |>.le.trans ( hc.length i ))) _ -- V let proof? 
lemma easy_T (H1:Vel P Z K ν x)(hc:TPaid P ν s A B)(hp: WarpHere false true P F u)(hx:WarpHere false true P H v)(he:Toned F)(hf:Toned H)(hv:nn u)(hh:nn v): HandC false false P ( zip2 Z K A B F H ) ( x*u*v ):= by
   obtain h:= cabin_T H1 hc hp hx he hf hv hh 0; rw [show Growth P.price s (x*u*v) 0=(x*u*v) from (by ext; simp [Growth])] at h; exact h
lemma unitFlow (a:I→ℝ)(h: Accel P a) : Adjuster (G:=G) P false true 1:= by have hV : 0 ≤ (if true=true then 1 else (0:ℝ)):=(by simp); obtain hf:= level (b:=false) (G:=G) h hV; rw [ show goodM P 0=(1: P.time→ℝ) from (by ext; simp [goodM])] at hf; exact hf
-- funds D.
variable {D:H_defect G I}{M:P.time→ℝ}{a:I→ℝ}
abbrev Cushion (P:Belt I)(D:H_defect G I): Prop:= ∀ z k,0<k→ WarpHere false true P ( D z k ) 1
variable (hf: Glow K)(he:RecipeD Z K X D)(hu:∀ n,Knits ( X n ))(hv:∀ z n, Knits ( D z n ))
include hf he hu hv
lemma ready_o (k:ℕ)(z:Half)(ht:0<k): LookS (warp0 G I ( D z k )) (bend G I ( ΦD K Z X D k z )):= by
    apply hooked (hv z k|>.1) ?_ ( he z |>.2 k ht |>.2 ); -- explicit crank Knits.V.
    refine ( knit_plus ( LiftE.knit ( gen_zip0 Z hf (loci Z z)) ( hv z k )) ( knit_plus ( knit_plus ( premium ( knit_smul (knit_birth ( hu k ) hf) _ ) _ ) ( knit_sum _ fun i hi=> knit_tree hf (hu _) (hv z _) )) ( knit_smul (knit_sum _ (fun i hi=> knit_sum _ (fun j hj=> knit_zip hf (hv i _) (hv z _)))) _ ))) |>.1
lemma D_gen (h: Vel P Z K ν 1)(H: bulk P X)(hs: Accel P a)(hP:∀ z k,0<k→ Lease false true P.price ( LaunchF P a (warp0 G I ( D z k )) ) 1)(hsd:∀ i j,i≠j→TPaid P ν M (loci Z i) (loci Z j)): Cushion P D:= by
    suffices hh:∀ k,0<k→∀ z,WarpHere false true P ( D z k ) 1 from fun z k h=>hh _ h z; intro k; induction k using Nat.strong_induction_on with| h k hg=>
       intro hk z; have h1 : nn (1:P.time→ℝ):= fun _=> zero_le_one; refine kernel hs ( ready_o hf he hu hv k z hk ) ( unitFlow a hs ) h1 (hP z k hk) ?_
       intro r hr hx; have hw:= Bolt ( A:=loci Z z ) h hx ( hv z k |>.1 ) h1; rw [ mul_one ] at hw; unfold ΦD coinF; rw [map_add]; apply Lens.plus hw; refine pinch (c:=false) ?p_cur (fun h=>Bool.noConfusion h); refine beauty ( beauty (adjustL (P:=P) _ h1 (fancy ?i _ )) ?t ) (fancy ?p _ ); -- ?i birth etc
       · apply Lease.sticks (a:=positive P.price 4 1 ( rateS P 4 )) (η_body h ( H k hk ) ( hu k |>.1 ) ( rateC _ _ )) ; intro i; exact le_of_eq (by simpa only [mul_one,Pi.one_apply,one_mul] using cashP i ( x:=1 ) ( y:=1 ) ( z:=1 )) -- use cashP
       · refine Cuba (P:=P) _ h1 (fun i hi=>?_); obtain hm:= early _ _ _ hi; simpa only [one_mul] using step_F ( H (k-i) (by omega) ) ( hg i hm.2 (by omega) z ) h.2.1 h1 h1
       exact Cuba _ h1 (fun i hi=> ( Cuba (P:=P) _ h1 (fun j hj=> by
            obtain H':=early _ _ _ hj; by_cases hi:i=z; · subst i; simpa only [one_mul] using ( spin_d (Z:=Z) h ( hg (k-j) (by omega) (by omega) z ) ( hg j (by omega) (by omega) z ) (hv z _|>.1) (hv z _|>.1) h1 h1 ( A:=loci Z z))
            simpa only [one_mul] using easy_T h (hsd i z hi) ( hg ( k-j ) (by omega) (by omega) i ) ( hg j (by omega) (by omega) z ) ( hv i _|>.1 ) ( hv z _|>.1 ) h1 h1 ))) -- semip
end YM.MS.Vista
