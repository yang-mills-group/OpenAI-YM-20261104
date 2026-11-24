import YM.FVA2.O.Dust.QRise
/-!
# Softened prices (negative t)

`Fairy` and `Stageable` only ask for `Royal` bounds. The shifts to put
inputs on the same center work well in this norm. `Sweep` means `Nilp`
estimate, a much stronger price used for the multi-mark difference terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Cool
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Osc MS.Osc.Snap MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors Fuse Job.Belt
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type} {F H:Glade G I}{p:I→ QP}{P:Geo I}{B:Deck G}{K: Booked B}{M: MS_Data G K}{x y:Rake.Site G I}
local notation "Qx"=> (east P false)
abbrev Fairy (P:Geo I)(F:Glade G I):= Royal (Lower P) (plug F)
lemma royalU (h:Known P F): Fairy P F:= by obtain ⟨q,h⟩:=h; exact ⟨_, fallen h ( b_le P )⟩
lemma Fair_unit : Fairy P (hori G I).unit:= by
    refine royalU ⟨0,?_ ⟩; intro E _ _ w hx hp; unfold Cape; simp only [stamp,zpow_zero,mul_one]; rcases w with _| ⟨i,w⟩; exact Costs.scalar (p:=fun _=>(1:ℂ)) ( Cost.of_le fun i p _=> by simp [ pitch,fieldDim ]); exact Costs.zero fun i p _=> length_p _ i
lemma Fairy.scale (h:Fairy P F)(c:ℂ): Fairy P (c • F):= r_smul h c
lemma Fairy.add (h:Fairy P F)(hx:Fairy P H): Fairy P (F+H):= Royal.add ( b_le P ) h hx
lemma Fairy.zero : Fairy P (0:Glade G I):= royalU Nilp.zero.known
lemma Fairy.sum (s:Finset W){f:W→Glade G I}(h:∀ i∈s,Fairy P (f i)): Fairy P (∑ i∈s,f i):= by classical induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact Fairy.zero| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=>h j (mem_insert_of_mem hj))
lemma Fairy.times (h: Fairy P F)(he: Fairy P H): Fairy P (joint G I F H):= Royal.P h he
abbrev Stageable (P:Geo I)(x:Rake.Site G I): Prop:= ∀ i,Fairy P (x i)
abbrev Sweep (P:Geo I)(x:Rake.Site G I): Prop:= ∀ i, Nilp P ( x i )
lemma castW (h:Stageable P x)(he:Stageable P y): Stageable P (bond G I x y):= fun k=> Fairy.sum (antidiagonal k) (fun i _=> (h i.1).times (he i.2))
lemma Sweep.unit : Sweep P (0:T ( Glade G I )):= fun _=> Nilp.zero
lemma Nilp.scale (h:Nilp P F)(c:ℂ): Nilp P (c • F):= Thin.scale h c -- parent.XT.
lemma Sweep.scale (h:Sweep P x)(c:ℂ): Sweep P (c • x):= fun i=> Nilp.scale (h i) c
lemma Sweep.add (h:Sweep P x)(he:Sweep P y): Sweep P (x+y):= fun i=> Nilp.add (h i) (he i)
lemma Sweep.sum (s:Finset W){f:W→Rake.Site G I}(h:∀ i∈s,Sweep P (f i)): Sweep P (∑ i∈s,f i):= by classical induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact Sweep.unit | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma Nilp.tags (h:Nilp P F)(he:Fairy P H): Nilp P (joint G I F H):= Thin.left ( b_le P ) h he
lemma Sweep.ljoint (h:Sweep P x)(he:Stageable P y): Sweep P (bond G I x y) := fun v=> Nilp.sum (antidiagonal v) (fun i _=> (h i.1).tags (he i.2))
lemma Nilp.jR (h: Fairy P F)(he: Nilp P H): Nilp P (joint G I F H):= Thin.right ( b_le P ) he h
lemma Sweep.rjoint (h:Stageable P x)(he:Sweep P y): Sweep P (bond G I x y):= fun v=> Nilp.sum (antidiagonal v) (fun i _=>Nilp.jR (h i.1) (he i.2))
-- behind shift <$uniform in unit scales all t<0>
def Fixed (p:I→QP): Prop:= ∃ C:ℝ,0<C∧∀ i,‖p i‖≤C
lemma Fixed.paid (h:Fixed p): paid (Lower P) (fun i=>‖p i.1‖) 1:= by obtain ⟨C,hC,hp⟩:= h; exact ⟨C,hC,0,fun i=>by simpa using hp i.1⟩
lemma untitled (h:Fairy P F)(he:Fixed p): Fairy P ( Serve.tilt G p F ):= by obtain ⟨k,h⟩:= h; exact ⟨k,grant_tilt h (Fixed.paid he)⟩
lemma Nilp.fixed (h:Nilp P F)(he:Fixed p): Nilp P ( Serve.tilt G p F ) := fun _=> recovery fun k=> grant_tilt ( fallen ( h k ) ( b_le P ) ) (Fixed.paid he)
lemma Arc_zero : Stageable P (glaze G I).unit:= by intro n; change Fairy P (SplitP.refineV SplitP.nat _ n); unfold SplitP.refineV; split; exact Fair_unit; exact Fairy.zero
variable [LinearOrder W] {X Y:Rake.Dance G I W}{S:Finset W}{ξ:Position W I}
lemma RootFixed (h:∀ i, Fixed (ξ i)): Fixed (rootX ξ S):= by unfold rootX; split; exact h _; exact ⟨1,zero_lt_one,fun i=>by simp⟩
def sector (G:Gauge)(I W:Type)[LinearOrder W]: Actors (Rake.Dance G I W) := (glaze G I).stack (SplitP.marked W)
lemma roy_pow (h:∀ s, Stageable P (X s))(S:Finset W)(n:ℕ): Stageable P ( (sector G I W).power X n S ):= by
    induction n generalizing S with| zero=> change Stageable P ( SplitP.refineV ( SplitP.marked W ) _ S ); unfold SplitP.refineV; split; exact Arc_zero; exact fun _=> Fairy.zero| succ n ih=>
    intro p; unfold power; change Fairy P (SplitP.Lift (SplitP.marked W) (bond G I) X _ S p); rw [SplitP.loan, Finset.sum_apply]; exact Fairy.sum _ (fun i _=> castW (h i.1) (ih i.2) p )
lemma dust_pow (h:∀ s, Sweep P ((X-Y) s))(hp:∀ s, Stageable P (X s))(he:∀ s,Stageable P (Y s))(S:Finset W)(n:ℕ): Sweep P (((sector G I W).power X n-(sector G I W).power Y n) S):= by
    let L:= sector G I W; induction n generalizing S with| zero=> unfold power; rw [sub_self]; exact Sweep.unit | succ n IH=>
    rw [power,power, Pi.sub_apply ]; change Sweep P ( SplitP.Lift (SplitP.marked W) (bond G I) X _ S- SplitP.Lift (SplitP.marked W) (bond G I) Y _ S); rw [ SplitP.loan, SplitP.loan, ← Finset.sum_sub_distrib ]; refine Sweep.sum _ (fun i _=>?_); let T:= bond G I; let U:=(glaze G I); let X0:= L.power X n i.2; let Y0:= L.power Y n i.2; change Sweep P (T (X i.1) X0-T (Y i.1) Y0); rw [show T (X i.1) X0-T (Y i.1) Y0=T ((X-Y) i.1) X0+ T ( Y i.1 ) (X0-Y0) from ( by simp only [ Pi.sub_apply,map_sub,LinearMap.sub_apply ]; abel ) ]; exact (Sweep.ljoint (h _) (roy_pow hp _ n)).add (Sweep.rjoint ( he _ ) (IH _) )
lemma dust_meal (h:∀ s, Sweep P ((X-Y) s))(hp:∀ s,Stageable P (X s))(he:∀ s, Stageable P (Y s)): Sweep P ( Meal X S-Meal Y S):= by
    unfold Meal Cheer cheers wages; simp_rw [Finset.sum_apply, Pi.smul_apply, ← Finset.sum_sub_distrib,← smul_sub ]; exact Sweep.sum _ (fun i _=> ( dust_pow h hp he S i ).scale _ )
end YM.FVA2.O.Cool
