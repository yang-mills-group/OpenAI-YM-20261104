import YM.MS.Vista.Eye
/-!
# Clocks transport, along r-ρ spacetime. Clip works at all t. Period comparison.At common common metric.S
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{P:Belt I}{ K L: Planet G I}{h Kx:P.time→ℝ}{F H X V:Glade G I} {x y:Law G}
  {A B:I→Cover}{b:Bool}{Z: Lin I}{μ: I→Measure QP}
-- expose absolute chart.K lamp. All motion facts retain b.Progress.N
abbrev zoom (K:Planet G I): Planet G I:= fun i t=> ( (exp t:ℝ):ℂ ) • K i (τ t)
abbrev Prune (P:Belt I)(b:Bool)(K:Planet G I)(Vp:P.time) : Latch.Edge G:= PaintP b ( zoom K ) Vp.1 ( tstart Vp )
abbrev Piece (P:Belt I)(K:Planet G I) (h:P.time→ℝ):=∀ b:Bool,Fund P.price ( Prune P b K ) h
lemma scalarη (b:Bool)(K:Latch.Edge G)(c:ℂ) : ηbone b (c • K)= c • (ηbone b K) := by
   cases b; · rfl
   funext i j p; change ( c*K i j p)* _ = c * ( K i j p*_ ); ring
lemma ΘpcFee (K:Latch.Edge G)(A:Cover)(X:Law G)(b:Bool)(μ:Measure QP)(c:ℂ): Θ_pc b μ A ( c • K ) X = c • Θ_pc b μ A K X:= by funext l; unfold Θ_pc; simp_rw [ Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_left_comm (be _ _) c, integral_const_mul ]
lemma weight_body (K: Latch.Edge G)(c:ℂ): birth ( c • K ) x=c • birth K x:= by funext w; simp_rw [birth,Hβ,detach, Pi.smul_apply,smul_eq_mul,mul_assoc, ← Finset.mul_sum,mul_left_comm (1/16:ℂ) c ]; rfl
lemma pair_fee (K:Latch.Edge G)(μ:Measure QP)(b:Bool) (A B: Cover)(c:ℂ): PairV b μ A B (c • K) x y=c • PairV b μ A B K x y:= by
    funext w; have hz (i j:BH G)(l r p): viν b (c • K) i j x y l r p=c*viν b K i j x y l r p:= by unfold viν; simp only [Pi.smul_apply,smul_eq_mul]; ring
    unfold PairV; simp_rw [ hz, mul_left_comm (be _ _) c,integral_const_mul, ← Finset.mul_sum,mul_left_comm (be _ _) c ]; exact map_smul ( allocate ( field parity ) w ) c _
-- Equalities from curve.L
abbrev Ap (P:Belt I){E:Type}(A:I→E)(p:P.time):= A p.1
lemma bend_q (H:Glade G I)(p:P.time): plug (bend G I H) p = ( ( exp (tstart p):ℝ ):ℂ) • H p.1 (τ (tstart p)):= rfl
abbrev actorP (P:Belt I)(F:Glade G I):= plug (J:=P.slot) ( warp0 G I F )
lemma wc_click (Z:Lin I): plug (bend G I ( click Z b A K F )) = pClock (Ap P Z.circ) b ( Ap P A ) (Prune P b K) ( actorP P F ):= by funext p; rw [bend_q]; change _ • Θ_pc b _ _ _ _=Θ_pc b _ _ (ηbone b ( (( exp (tstart p):ℝ):ℂ ) • _)) _; rw [scalarη, ΘpcFee]; rfl
lemma expP : plug (bend G I (expJ K F H))=(fun i:P.time=> tree parity ( Prune P false K i ) ( actorP P F i ) ( actorP P H i )):= funext fun i=> by rw [bend_q, show Prune P false K i=_ from rfl ]; exact ( Wind.lineT .. )|>.symm -- period using μzone but formula general K
lemma weightFC : plug (bend G I (term_birth K F))=(fun i:P.time=> birth ( Prune P true K i ) ( actorP P F i )):= by funext i; rw [bend_q]; change ( _ :ℂ ) • term_birth K F _ _=birth (ηbone true ( ((_ :ℝ):ℂ) • _ )) _; rw [scalarη,weight_body]; rfl
lemma bend_adj (X: Glade G I) : bend G I (adjust b X)=adjust b (bend G I X):= by
   cases b; · unfold adjust; simp only [Bool.false_eq_true,↓reduceIte,map_zero];
   rfl
abbrev env (b:Bool)(A B:Faces I): Faces I:= fun i=> Dph b (A i) ( B i )
lemma wc_region : plug (bend G I ( feeling Z b A B K F H ))= Window b (Ap P ( A-B )) (Ap P (env b A B)) ( Ap P Z.circ ) ( Prune P b K ) (actorP P F) ( actorP P H ):= by funext i; rw [bend_q]; change ( _ :ℂ) • _= PairV b _ _ _ ( ηbone b ( ( _:ℂ ) • _ ) ) _ _; rw [scalarη,pair_fee]; rfl
lemma footage (H: Glade G I)(he:Toned H): Visible (actorP P H):= ⟨ fun i=> he.sound _ _, fun i=> by intro E _ _ f w hw ht; exact (he.touch i.1) E (fun _=>τ (tstart i)) w hw contDiff_const ⟩ -- shadow _ `f` binder log Prop. λ no time. parse
end YM.MS.Vista
