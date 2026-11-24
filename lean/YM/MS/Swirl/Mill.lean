import YM.MS.Swirl.LandLine
/-!
# Mill actual regulator covariance side Side, not double.Pay factors cross-check mesh handed in.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl.Near
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice City Latch Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program
open Complex (I)
open Tone.Frame
open scoped Topology ContDiff Interval
variable {G:Gauge}{A E:Type}{n:Side}{b:Bool}
-- Wellness.S.IR
lemma BankK : Twig ( FinalK G ):= by
   obtain h:= foe G 1; constructor
   · rintro i j _ q ⟨x,rfl⟩; simp_rw [ and_here ]; unfold bank; rw [ sq_stamp, h.pin i j ⟨ x,rfl ⟩ ] -- ambiguous pin
   · intro i j q; rw [ and_here,and_here,h.t ]; rw [ wave_neg,bank,bank,sq_neg,mul_left_comm ]
   · intro i j q; rw [ and_here ]; exact fun p=> h.close _ _ _ ( right_ne_zero_of_mul p )
   intro i j q; rw [ and_here,and_here,h.gov, wave_neg,bank,bank,sq_neg ]; exact Eq.symm (mul_assoc (bank (wave q)) (LaceL G 1 i j q) _ )
lemma dawnForest : Forest G 0=0:= by funext i j p; unfold Forest dope Landau.choir; split <;> simp [Fuel,ohLow]
lemma tClose (t:ℝ): Flux.closed ( Forest G t ) parity false:= Dk_cl (City.closure wave (show Flux.closed ( Fuel t ) Landau.p false from (by rintro ⟨_|i,_|_⟩ ⟨_|j,_|_⟩ p <;> ( first | exact fun _=>rfl | simp [Fuel,Tail]))))
-- geometry
abbrev Master (G:Gauge)(n:Side)(b:Bool):= Paper n b ( FinalK G )
lemma zeroM (t:Bool): Clear σbranch ( Master G n t ):= readsK BankK.close t
lemma paySym (t:Bool): Cog.Sym σbranch ( Master G n t ):= by
    cases t; · exact stampL BankK.pin BankK.t
    exact symC ( riverOK BankK.pin BankK.gov ) (stampL BankK.pin BankK.t)
lemma mat_D (t:ℝ)(x y:FixedMode G n): HasDerivAt (fun s=> mat n ( Forest G s ) x y) ( mat n ( LaceL G t ) x y ) t:= by unfold mat EdgeV; split; exact (clave x.1 y.1 (Coord x.2) t).const_mul _; exact hasDerivAt_const ..
lemma mat_L (x y:FixedMode G n): Tendsto (fun t=>mat n ( Forest G t ) x y) atTop (𝓝 ( mat n (FinalK G) x y )):= by unfold mat EdgeV; split; exact ( essence x.1 y.1 (Coord x.2)).const_mul _; exact tendsto_const_nhds
abbrev Parks (G:Gauge)(n:Side)(b:Bool): Lines ( FixedMode G n ):= fun t=> Paper n b ( Forest G t )
lemma powerH (G:Gauge)(n:Side)(b:Bool): Wellness σbranch ( Parks G n b ) ( normal G n b ) (Master G n b):= by
   constructor
   · funext x y; unfold Parks; rw [ dawnForest ]; cases b <;> simp [Paper,imageV,Cascade,imageW,mat,EdgeV]
   · intro a w t; cases b; · exact mat_D t a w
     exact (mat_D t a w).add ( ( mat_D t a (( iota G n ).mode w) ).mul_const _ )
   · intro t; exact readsK ( tClose t ) b
   intro i j; cases b; exact mat_L i j; exact ( mat_L i j ).add ( ( mat_L i (( iota G n ).mode j) ).mul_const _ )
end YM.MS.Swirl.Near
