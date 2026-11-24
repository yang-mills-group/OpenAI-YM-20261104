import YM.OPE.Compatible.Frog.Pluck
/-!
# program push. banach output weights differing
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ} {C:KernelChoices}
variable {τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
abbrev Forget (p:Seat k m I)(h:l≤m):Seat k l I:=fun i=> down I i.val m l h (p i) -- ambiguity
lemma forgets (p:Seat k m I)(h:l≤m): lilies l k I (Forget (m:=m) p h)=lilies m k I p:=by
      funext i; by_cases hp:i≤k
      · rw [soup,soup,moduleAt,dif_pos hp,moduleAt,dif_pos hp]; let L:Fin (k+1):=⟨i,show i<k+1 from Nat.lt_succ_of_le hp⟩; let z:= seed m i I (p L); change seed l _ I (down I i m l h (p L))= _; exact (show _ from botany l z ‖p L‖ (soot_le_k z _ (humor (m:=m) _) h)) -- infer L binder
      rw [(sproutV l _ _).1 _ (by omega),(sproutV m _ _).1 _ (by omega)]
noncomputable def glasses (I:Type)(k m l:ℕ)(h:l≤m): Seat k m I→L[ℝ] Seat k l I:= ContinuousLinearMap.pi fun i=> down I _ m l h ∘L ContinuousLinearMap.proj i
lemma putG (p:Seat k m I) (h:l≤m): glasses I k m l h p=Forget p h:=rfl
-- real turns before calendar
variable {K:Sponsor G}{T:Seasons K}{v b:ℝ} {P:Patch}
structure RollD (A:Alps K T i v) (U:Boxes G P C) (R:ChartRatio G):Prop where
     flea : G.Simple
     jar : LocalRatio R
     eph : Era U A
variable (b:ℝ)(A:Alps K T i v)(U:Boxes G P C)(R:ChartRatio G)
variable (h:RollD A U R)(hp: Aware d τ)

-- define complete flow on T!
lemma awareLeaf (hp:Aware d τ)(i:Phase):45≤τ i:=by have h:=hp.credit i; omega
noncomputable def chamber (b:ℝ)(x y:Phase)(h:RollD A U R)(hp:Aware d τ) : Seat (d+x.val) (τ x) (Shade G)→L[ℝ] Seat (d+y.val) (τ y) (Shade G):= if ht:x≤y then glasses (Shade G) _ (τ x) _ (hp.mono ht) ∘L sectorOp P C A U R b (awareLeaf hp x) d x y h.flea h.eph h.jar else 0
noncomputable def actor (b:ℝ)(h:RollD A U R)(hp:Aware d τ): Tower (Shade G) d τ→L[ℝ] Tower (Shade G) d τ:= ContinuousLinearMap.pi fun i:Phase=> ∑ j:Phase,chamber A U R b _ i h hp ∘L (ContinuousLinearMap.proj j)
lemma lemmaE (p: Tower (Shade G) d τ)(y:Phase): spread G d τ p y= (pointer G d y (τ y) (p y)) y:= by rw [pointerX, show _= _ from (show impulse y (lilies (τ y) _ _ (p y)) y=_ from Pi.single_eq_same ..)]; rfl
lemma actorA (p:T!)(i:Phase): actor A U R b h hp p i= ∑ j:Phase, chamber A U R b j i h hp (p j):=by unfold actor; rw [ContinuousLinearMap.pi_apply,_root_.sum_apply];rfl
lemma actsP (p:T!)(i j:Phase):
     lilies (τ j) _ _ (chamber A U R b i j h hp (p i))=sculpt P C U A R b (pointer G d i (τ i) (p i)) d j:=by
                                                                                                            unfold chamber; split
                                                                                                            next ht => rw [ContinuousLinearMap.comp_apply,putG,forgets]; exact publicity ..
                                                                                                            next ht=> rw [_root_.zero_apply,map_zero, ← publicity P C A U R b h.eph h.flea h.jar (awareLeaf hp i) d i j (p i),shadowZero P C A U R b h.eph h.flea h.jar (awareLeaf hp i) _ _ _ (by order),_root_.zero_apply,map_zero]
lemma pointers (p:T!): spread G d τ p=∑ i:Phase,pointer G d i (τ i) (p i) :=by
       funext i; rw [Finset.sum_apply, Finset.sum_eq_single i]; exact lemmaE p i ; intro j _ hj; rw [pointerX]; unfold impulse; simp [Ne.symm hj]; simp
