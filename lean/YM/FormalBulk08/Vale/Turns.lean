import YM.FormalBulk08.Vale.Sabre
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
/-! Product extends to Wick waves, no analysis pay at r=0 of potential;
 only use Kalm for Marked. General StepH flow identity. Use recursion over list of
 input letters ($j,l$) given by filtered stencils. -/

def pebbleW (V:Type*): Waves V:= fun n=>if n=0 then bead V else 0
lemma bead_cove [Fintype V]: pebbleW V=Lava.posting (1:Heat ℝ V):= by
   funext n e r; unfold pebbleW; by_cases he:n=0
   · subst n; rw [if_pos rfl,←one_bead]; unfold Lava.posting; rw [read_initial, early,map_one]; rfl
   rw [if_neg he];symm;unfold Lava.posting readSlice; rcases e with (_|e) <;> simp_rw [coeff_one]
   all_goals simp [he, Polynomial.coeff_one,marble_zero]

def campfire (P: I→ Waves V): List I→ Waves V
   | [] => pebbleW V
   | i::l=>doubled (P i) (campfire P l)
lemma campH [Fintype V](P:I→Heat ℝ V)(L:List I): campfire (fun i=>Lava.posting (P i)) L=Lava.posting (L.map P).prod:= by
    induction L with
    | nil=> exact bead_cove
    | cons i S ih=> rw [List.map_cons,List.prod_cons,posted,campfire,ih]
/-- which interactions definitely pay the two distinct column roots?
`scatter` only the heat carré between $p$ and independents. -/

def scatter (q:V→V→ℝ)(P:Waves V)(Q:I→Waves V): List I→Waves V
   | []=>0
   | i::l=>doubled (brawl q P (Q i)) (campfire Q l)+ doubled (Q i) (scatter q P Q l)

def collision (q:V→V→ℝ)(Q:I→Waves V): List I→ Waves V
   | []=>0
   | i::l=> scatter q (Q i) Q l + doubled (Q i) (collision q Q l)

variable [Fintype V](q:V→V→ℝ)
lemma readings (p P: Heat ℝ V): posting (crossHeat q p P)= brawl q (Lava.posting p) (Lava.posting P):= by
    funext n e r; rw [Lava.posting, read_cross, stone_crest]
lemma posting_front (p P: Heat ℝ V): posting (p + P)= Lava.posting p + Lava.posting P:= by
    funext a b c; rw [Lava.posting,read_add,←canyon_eq,map_add]; rfl
@[simp] lemma posting_empty (V:Type*)[Fintype V]: Lava.posting (0:Heat ℝ V)=0:= by funext a b c; simp only [Lava.posting,readSlice,map_zero, Polynomial.coeff_zero,marble_zero]; rfl
lemma cross_tide (p t u:Heat ℝ V): crossHeat q p (t*u)=crossHeat q p t*u+ t*crossHeat q p u:= by
   simp_rw [crossHeat,Derivation.leibniz,smul_eq_mul, Finset.sum_mul,Finset.mul_sum,mul_add,←Finset.sum_add_distrib];apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
lemma scatter_floats (p:Heat ℝ V)(P:I→Heat ℝ V)(L:List I): scatter q (Lava.posting p) (fun i=>Lava.posting (P i)) L=posting (crossHeat q p ((L.map P).prod)):= by
   induction L with
   | nil=> simp [scatter,crossHeat]
   | cons i l ih=> rw [List.map_cons,List.prod_cons,cross_tide,posting_front,posted,posted,readings,scatter,ih,←campH]

def pile (P:I→Heat ℝ V): List I → Heat ℝ V
   | []=>0
   | i::l=> crossHeat q (P i) ((l.map P).prod) + P i*pile P l
lemma pile_cast (P:I→Heat ℝ V)(L:List I): Lava.posting (pile q P L)=(collision q (fun i=>Lava.posting (P i)) L):= by
    induction L with
    | nil=> rw [pile,collision,posting_empty]
    | cons i l ih=> rw [pile,collision,posting_front,posted,ih, ← scatter_floats]
-- internal time factor all interactions through G powers
lemma incidents (A:Heat ℝ V)(P:I→Heat ℝ V)(L:List I)(h:∀ i∈L,shaft Polynomial.derivative' (P i)=cinder q (P i)+2*crossHeat q A (P i))(hs:∀ i j,q i j=q j i): let V:=(L.map P).prod; shaft Polynomial.derivative' V=cinder q V+2*crossHeat q A V -2*pile q P L := by
   induction L with
   | nil=> intro V'; simp only [show V'=1 from rfl, track,crossHeat, pile, Derivation.map_one_eq_zero, _root_.map_zero];simp
   | cons i k ih=>
     obtain hp := ih (fun i hx=> h i (List.mem_cons_of_mem _ hx)); let V:=(k.map P).prod; rw [List.map_cons,List.prod_cons]; intro _; change shaft Polynomial.derivative' (P i*V)=_; rw [Derivation.leibniz, hp, h i List.mem_cons_self]; dsimp only [pile]
     change (P i* _+ V* _)= cinder q (P i*V)+2*crossHeat q A (P i*V)-_;rw [cinder_prod,cross_turn q hs V (P i),cross_tide];unfold V;ring
lemma crew_cause (f:Pap V)(U:I→Pap V)(L:List I)(h:coeff 0 f=0)(hs:∀ i j,q i j=q j i)(F:Pap V)(hF:F=(L.map U).prod):
    let B := flare q f F; let P:=fun i=> flare q f (U i); let W:= B-(L.map P).prod
    early W=0 ∧ shaft Polynomial.derivative' W=cinder q W+2*crossHeat q (coal q f) W+2*pile q P L := by
   intro B P W
   have ha: PowerSeries.map (Polynomial.evalRingHom 0) ((L.map P).prod)=(L.map U).prod:= by
       clear hF W; induction L with
       | nil=>simp
       | cons i l ih=> rw [List.map_cons,List.prod_cons,_root_.map_mul,ih,← early, show early (P i) = _ from flare_initial q f (U i) h]; simp
   constructor
   · unfold W early; rw [map_sub,ha]; change early _ - _=_; rw [flare_initial _ _ _ h,hF,sub_self]
   let V:=(L.map P).prod; have hp:= incidents q (coal q f) P L (fun i _=> flare_deriv q f (U i) h hs) hs
   unfold W; rw [_root_.map_sub,hp,_root_.map_sub,show shaft Polynomial.derivative' B= _ from flare_deriv q f F h hs]
   have he : crossHeat q (coal q f) (B-V)= crossHeat q (coal q f) B-crossHeat q (coal q f) V:= by simp_rw [crossHeat,_root_.map_sub,mul_sub, Finset.sum_sub_distrib]
   rw [he]; unfold V B; ring
end YM.FormalBulk08.Vale
