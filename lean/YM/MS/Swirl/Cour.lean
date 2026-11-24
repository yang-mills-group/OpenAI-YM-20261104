import YM.MS.Swirl.Calm
/-!
# Uncolored Green after based position mesh projection
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl.Near
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Frame Lattice City Latch Detect Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Complex (I)
open scoped Topology ContDiff Interval
variable {G:Gauge}{A E:Type}{n:Side}{b:Bool} [Fintype A]
local notation "C"=> mat n ( FinalK G )
local notation "S"=> sleeve lace ( s₀ G )
abbrev flatH (G:Gauge)(n:Side): BL (FixedMode G n):= Bulk G n (sleeve lace ( s₀ G ))
variable (w:Tag→ℂ) (a d i j:BH G) (p q r:Site n)
local notation "H"=> flatH G n
lemma ChillK (x y:BH G)(p:Site n): Chill C (x,p) (y,-p) = scaleZ n * Bass G x y (Coord p):= by change 2 * ( mat n _ ( x,p ) _ )=_; unfold mat; dsimp only; rw [neg_neg, if_pos rfl ]; unfold EdgeV FinalK; ring
lemma chillOff (x y: BH G)(p q:Site n)(h:q≠ -p): Chill C (x,p) (y,q)=0:= by unfold Chill mat; rw [ if_neg (show ¬p= -q from fun he=>h (by rw [he,neg_neg])), mul_zero]
lemma sailK : Speaks S:= volt ( City.Perk.perk_origin _ (( crisp G 0 ).symm))
lemma Neg_S : H [(i,-p),(j,p)] = brightness n * ((lace ( i,-Coord p ) * lace ( j,Coord p )) * styleK (-(Coord p)) i j):= by
    rw [flatH,bulkZ, if_pos ( show net [(i,-p),(j,p)]=0 from (by simp [net]) ), Orbit.point ]; rw [sailK (Orbit.stage [(i,-p),(j,p)]) [( i,-Coord p ),( j,Coord p )] (.cons ( show peer _ _ from ⟨rfl,( ξ_neg p ).sym⟩ ) (.cons ⟨rfl, congrQ.normal _⟩ .nil)) ]; rw [ sleeve_here,show s₀ G [( i,-Coord p ),( j,Coord p )]=styleK (-Coord p) i j from (by simpa using rankTwo (-Coord p) i j) ]; simp [hook]
-- K endpoints letters
abbrev sz (p:QP)(a b:BH G):= Landau.choir Tail wave a b p
lemma νX : Chill C (a,p) (i,-p)* H [(i,-p),(j,p)] * Chill C (j,p) (d,-p)= scaleZ n * ( Orbit.flag a (Coord p)* Orbit.flag d (-Coord p) )*( sz (Coord p) a i * styleK (-Coord p) i j * sz (Coord p) j d ):= by
    rw [ ChillK,ChillK,Neg_S ]; unfold Bass; let z:= Coord p; let X (b c:BH G):= sz z b c
    calc
      _ = scaleZ n * brightness n * ((Orbit.flag i (-Coord p)*lace (i,-Coord p)) * (Orbit.flag j (Coord p)*lace (j,Coord p))) * (scaleZ n * ( Orbit.flag a (Coord p)* Orbit.flag d (-Coord p) )*( X a i * styleK (-Coord p) i j * X j d )) := by unfold X z sz; ring
      _ = _:= by rw [lightW, show Orbit.flag i (-Coord p)*lace (i,-Coord p)=1 from lace_ (i,-Coord p), show Orbit.flag j (Coord p)*lace (j,Coord p)=1 from lace_ (j,Coord p) ]; simp [ X,z ]
lemma S_hold (h:r≠p): H [(i,-p),(j,r)] =0:= Gps _ n _ (by simpa [ net, neg_add_eq_zero ] using (Ne.symm h))
lemma twistD (a d:BH G)(p q:Site n): ∑ i:FixedMode G n,∑ j:FixedMode G n, w ( Eyes i ) * Chill C (a,p) i * H [i,j]*Chill C j (d,q) = ∑ i:BH G,∑ j:BH G, w ( Tagged i ) * ( Chill C (a,p) (i,-p) * H [(i,-p),(j,p)] * Chill C (j,p) (d,q)) := by
    simp_rw [ Fintype.sum_prod_type (α₁:=BH G) ( α₂:=Site n ) ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [ Finset.sum_eq_single_of_mem (-p) (Finset.mem_univ _ ) ];
    · refine Finset.sum_congr rfl fun j _=>?_ ; rw [ Finset.sum_eq_single_of_mem p ( Finset.mem_univ _ ) ]; · rw [ mul_assoc ( w ( Eyes _ )) ]; rw [ mul_assoc ( w ( Eyes _ )) ]
      intro k hk ht; rw [ S_hold i j p k ht ]; ring
    intro k hk ht; simp only [ chillOff a i p k ht ]; simp
lemma Θgreen (w:Tag→ℂ): Green ( w ∘ Eyes ) C H:= by
    refine ⟨?_⟩; rintro ⟨x,p⟩ ⟨z,q⟩; unfold Function.comp; rw [ twistD ]; by_cases ht:q= -p; swap; · simp_rw [ show ∀ i:BH G,Chill C ( i,p ) ( z,q )=0 from fun i=> chillOff i z p q ht ]; simp
    subst q; simp_rw [ νX ]; rw [ChillK];
    simp_rw [ show ∀ i j:BH G, w ( Tagged i ) * ((scaleZ n * ( Orbit.flag x (Coord p)* Orbit.flag z ( -Coord p )))*( sz (Coord p) x i * styleK ( -Coord p ) i j * sz (Coord p) j z ))= (scaleZ n * ( Orbit.flag x (Coord p)* Orbit.flag z ( -Coord p ))) * ( w ( Tagged i ) * sz (Coord p) x i * styleK ( -Coord p ) i j * sz (Coord p) j z ) from fun i j=>by ring, ← Finset.mul_sum, sz, sesame ]; unfold Bass; change _= -w (Tagged z)*_; ring
end YM.MS.Swirl.Near
