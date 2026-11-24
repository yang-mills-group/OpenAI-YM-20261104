import YM.FVA2.O.Dust.Cinder
/-!
# Estimates for QR in the UV (t ≤ 0). Work *before* multiplication by loose external phases.
B normalized with weight -1 as opposed to even smoothing derivative.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Cool
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Osc MS.Osc.Snap MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors Fuse Job.Belt Alps Outlook
open scoped Topology ContDiff Interval
variable {G:Gauge}{I:Type}{F H:Glade G I}{U:Planet G I}{T:Scale I}{f:I→ Law G}{z η:I→ℝ}{q b:ℤ}{P:Geo I}{B:Deck G}{K:Booked B}{M:MS_Data G K}{X:Rake.Site G I}
local notation "Qx"=> (east P false)
local notation "m0"=> (fun _:I=>planeF)
local notation "uB"=> (fun _ : I=> lineB G)
lemma χB : Sheet (Lower P) (stamp (Lower P) (-1)) (plug uB):= by
    obtain he:= edgeT ( t:=tstart ) ( Lower P) (fun i=>( coldE P i ).symm) (shapeB (G:=G)) rB; unfold stamp; simp_rw [zpow_neg_one]; exact he
lemma Z_table (h:∀ i,exp (η i)=T.length i)(u v:BH G): Bound T (fun _=>(Wick.Q G 0).table u v ) (stamp T (wfield u-wfield v-1)):= by
    let X:=(Wick.Q G 0).table u v; let q:ℤ:=wfield u-wfield v-1; have he(s:ℝ): Bench.Forest.patch X q s=X:= by
        funext p; unfold Bench.Forest.patch X; rw [ ← lawQ G, mul_right_comm (_*_ :ℂ), ← mul_assoc, ← amount_add,← amount_add,← amount_add, show (q:ℂ)+ ( wfield v+ -(wfield u:ℂ) + 1 )=0 from ( by push_cast [q]; ring ), Azero,one_mul ]
    obtain hp:=Outlook.bound_r T h q ( ( Wick.count_caps G ).solid 0 u v ); simp_rw [show ∀ i:I,Bench.Forest.patch (( Wick.Q G 0).table u v) q (η i)=_ from fun i=> he (η i) ] at hp; exact hp
lemma lease_Q (h:∀ i,exp (η i)=T.length i)(hp:Latch.Lease false false T f z)(hh: Latch.nn z): Latch.Lease false false T (fun i=> ( Wick.Q G 0 ).raise (f i)) (stamp T (-1)*z):= by
    intro E _ _ w hx hb; unfold Cape Chart; simp_rw [visit_Z,visit_sail];
    have hNN i : 0≤T.length i ^ pitch w*( stamp T (-1)*z ) i := mul_nonneg ( length_p .. ) ( mul_nonneg (posS i|>.le) (hh i) )
    refine visit_bound ?_ (fun l i k H=> ?_); exact hNN
    refine Costs.sum Finset.univ (fun j _=>?_) (fun i p _=> hNN i); obtain he:= Costs.mul ( Bound.linear i.2 (Z_table h i.1 j) ) (hp E (l++(j,i.2)::k) (fun i=>Bool.noConfusion i) (fun i=>Bool.noConfusion i)); convert he using 1; ext1 i; ext p; simp only [Chart,sail_join,sail_cons]; funext i' p; unfold stamp pitch; simp only [visit_field,H,Pi.mul_apply]; rw [← mul_assoc,← mul_assoc,← zpow_add₀ ( T.pos i'|>.ne'), ← zpow_add₀ ( T.pos i' |>.ne' ) ]; congr 2; omega
lemma Nilp.loopB (h:Warm F false)(he:Nilp P F): Nilp P ( Rcy uB F ):= by
    rw [ spine h realityB ]; intro v; have hp: Latch.nn ( stamp ( Lower P ) (-1) ):= fun _=>posS _|>.le; obtain hx:= planC (K:=plug uB) (( he (v+1)).highp) χB (Tall (Lower P) 5 (by omega)) (fun E _=>tom ( Lower P ) 5 (by omega)) (fun _=> posS _|>.le ) hp; rw [← stampA, show (-1:ℤ)+(v+1)=v from (by omega)] at hx; exact hx
lemma Nilp.treeB {n:ℕ}(h:Nilp P F): Nilp P ((both G I).C ((Lives.gather M P.η) n) F) := by
    intro v; apply Latch.Lease.sticks ( trunks ( S:=Lower P ) (fun i j=> Latch.polar ( χB (G:=G) i j )) ((safeB ( M:=M ) (P:=P) (i:=n)).snow.highp) ( (h (v+1)).highp ) (fun i=>posS _|>.le) (fun i=>posS _|>.le) (fun i=>posS _|>.le)); intro i; apply le_of_eq; simp only [positive, stamp, Pi.mul_apply, zpow_add₀ ( show (Lower P).length i ≠0 from ( (Lower P).pos i ).ne' ) ]; field_simp [( (Lower P).pos i ).ne']
lemma Nilp.Qop (he:Nilp P F) : Nilp P ( Lives.Z G I F ):= by
    intro k; obtain hh:= lease_Q ( η:= tstart ) ( T:=Lower P ) (fun i=>( coldE P i).symm) ( he (k+1) ) (fun i=>posS _|>.le); rw [ ← stampA, show -1+(k+1)=k from (by omega)] at hh; exact hh
lemma Nilp.navs (he: ∀ n,Nilp P ( X n ))(hp:∀ n,Warm (X n) false)(n:ℕ): Nilp P ( nav M P.η X n ):= by
    change Nilp P ((both G I).J _ + pairW (both G I).C (Lives.gather M P.η) X n); rw [ paired,front G I,LinearMap.add_apply ]; exact (( he n|>.Qop ).add ( Nilp.loopB ( hp n ) ( he n ))).add ( Nilp.sum _ (fun i _=> Nilp.treeB ( he i.2 ) ) )
end YM.FVA2.O.Cool
