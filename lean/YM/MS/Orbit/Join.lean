import YM.MS.Orbit.PC
/-!
# Frames on anchored pair in Period. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Flux Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{P:Latch.Edge G}{F H: Law G}{n:Side}{A B: Cover}
local notation "Z"=> field ( parity ( A:=Axis ) ( C:=G.ColorIndex))
lemma ConK (b:Bool)(h: Twig P)(F H:Than G n): conn Z (faceκ b n P) F H= ∑ q:Site n,∑ i:BH G,∑ j:BH G,(scaleZ n * ηbone b P i j (Coord q)) • ( (2:ℂ) • Head Z (i,q) (j,Omega ( Site n) b q) F H ):= by
    have hx:= riverOK (n:=n) h.pin h.gov; rw [ ← κFocus (P:=P) ( b:=b ) (fun i j=> (2:ℂ) • Head Z i j F H), pair_line (show Clear Z _ from ?_) (show Cog.Sym Z _ from ?_) F H ]; simp_rw [ mul_smul, smul_comm _ (2:ℂ) ]; · cases b; exact evenK h.close; exact clear_i (S:=iota G n) ( evenK h.close ); -- proof linear
    cases b; exact stampL h.pin h.t; exact sym_i hx ( stampL h.pin h.t )
-- unpack from ∫ sum and use allocate.S
variable {x y z: Legs (FixedMode G n)}
lemma point_at (p:Cover)(A: Law G)(v:Legs (FixedMode G n))(i:BH G)(q:Site n): anchor G n p A ((i,q)::v)= Φa p q*Φa p ( net v )* A ((i,Coord q)::stage v):= by rw [chase_now,net_cons, φ_first,point ]; rfl
lemma point_off (p:Cover)(i:BH G)(q:Site n)(H:Speaks F)(b:Bool): anchor G n p F ((i,Omega _ b q)::x) = Φa (taste b p) q * Φa p (net x)* F (( i,Opp b (Coord q) ):: stage x):= by rw [point_at, H ((i,Coord (Omega _ b q))::stage x) ((i,Opp b (Coord q))::stage x) (.cons ⟨rfl,pCharge q _⟩ (asc _)),φ_other ]
lemma net_a (h:Split x y z): Φa A (net x) * Φa B (net y)= Φa B (net z) * Φa (A-B) (net x):= by nth_rw 1 [show A=A-B+B from (by abel)]; rw [φ_start,← split_net h,φ_first]; ring
lemma scat_δ (w:Legs (FixedMode G n))(F:Shared ( Lane4 G ) ℂ): scatter Z (stage w) F=scatter Z w (fun x y=> F (stage x) (stage y)):= by
   induction w generalizing F with| nil=> rfl| cons i l ih=> rw [ show stage (i::l)= addr i::stage l from rfl, scatter_cons, ih, scatter_cons]; congr 1; funext x y; rw [Λ_d]; rfl
-- kernel.Body:
lemma componentR (b:Bool)(h:Speaks H)(hp:Split x y z)(q:Site n) (i j:BH G):
  scaleZ n * ηbone b P i j (Coord q) * ( (2:ℂ) * (cross (parity j) (degree Z x) * (anchor G n A F ((i,q)::x)) * (anchor G n B H ((j,Omega _ b q)::y)))) =
      Φa B (net z) * (be (A-B) (net (stage x)) * ( scaleZ n * (be ( Dph b A B ) ( Coord q ) * viν b (ηbone b P) i j F H (stage x) (stage y) (Coord q)))):= by
   unfold viν Dph; rw [point_at,point_off _ _ _ h, Λ_d, ← φ_s, ← φ_c, φ_start]; -- implicit b from pointoff.Not likely rw without b.Spec.
   linear_combination (norm:=ring_nf) (scaleZ n * ηbone b P i j (Coord q)*(2:ℂ)*cross (parity j) (degree Z x) * F ((i,Coord q)::stage x) * H ((j,Opp b (Coord q))::stage y) * Φa A q * Φa (taste b B) q)*(net_a (A:=A) (B:=B) hp)
lemma A_T (b:Bool)(h:Twig P)(hv:Speaks H): conn Z (faceκ b n P) (anchor G n A F) (anchor G n B H)= anchor G n B ( PairV b (σcap n) (A-B) (Dph b A B) ( ηbone b P ) F H ):= by
   funext z; rw [ ConK b h]; let T:=allocate Z z ( R:= ℂ );
   rw [chase_now]; conv_rhs=> rw [point, PairV,scat_δ ]
   simp_rw [ Finset.sum_apply, Pi.smul_apply, head_R ]; -- rewrite not under sleeve? `PairV def unfolds C?`
   -- convert scatter to allocate inside
   simp_rw [ show ∀ K: Shared ( FixedMode G n ) ℂ, scatter Z z K=T K from fun _=> rfl, ← map_smul T, ← map_sum T ];
   change T _= Φa B (net z) • T _; rw [ ← map_smul ]; apply scatter_congr
   intro l r hl; simp only [ Finset.sum_apply, barkU, Pi.smul_apply,smul_eq_mul, Finset.mul_sum ]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k hk=> componentR b hv hl k i j
end YM.MS.Orbit
