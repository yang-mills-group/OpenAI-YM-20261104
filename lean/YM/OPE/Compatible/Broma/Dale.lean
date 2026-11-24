import YM.OPE.Compatible.Jess.Yen
import YM.OPE.Compatible.Kiosk.Knit
/-!
# Dual Tau billing at all orders
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose
variable {n c f:Side}{I J M:Type}{G:Gauge}{r i j d m l k:ℕ}{τ:Phase→ℕ}
section fares
variable {x p v:M→ℝ} {X Y:M→Script I d}{σ C:ℝ}
structure Auger (m:ℕ)(X Y:M→Script I d)(v x:M→ℝ) :Prop where
     A : Loan m X 1 x
     B : Loan m Y 1 x
     D : Loan m (X-Y) v x
structure Silk (σ:ℝ)(X Y:M→ Row I J)(v x:M→ℝ):Prop where
     A : Tip σ X 1 x
     B : Tip σ Y 1 x
     D : Tip σ (X-Y) v x
lemma slicesP (h:Fin d≃ Fin j)(p:Loan m X v x): Loan m (fun i=> Shell.slice h (X i)) v x:=by obtain ⟨a,b,y,H⟩:=p; exact ⟨a,b,y,fun i=>slice_fee _ _ (H i)⟩
lemma auger_s (g:Fin d≃ Fin j)(h:Auger m X Y v x):Auger m (fun i=> Shell.slice g (X i)) (fun i=>Shell.slice g (Y i)) v x:=⟨slicesP g h.A,slicesP g h.B,slicesP g h.D⟩
lemma plusA {Z W:M→Script I d}(h:Auger m X Y v x)(hp:Auger m Z W v x)(hx:1≤ x)(hz:0≤ v): Auger m (X+Z) (Y+W) v x:= by
     refine ⟨Loan.seize h.A hp.A hx zero_le_one, Loan.seize h.B hp.B hx zero_le_one,?_⟩; rw [add_sub_add_comm]; exact Loan.seize h.D hp.D hx hz
lemma nilA (x v:M→ℝ)(I:Type)(r:ℕ)(m:ℕ): Auger (I:=I) (d:=r) m 0 0 v x:=by refine ⟨Loan.zero m _, Loan.zero m _,?_⟩; rw [sub_zero]; exact Loan.zero m _
lemma Aset (P Q:J→M→Script I d)(t:Finset J)(h:∀ i∈t, Auger m (P i) (Q i) v x)(hx:1 ≤ x)(hp:0 ≤ v): Auger m (fun i=>∑ j∈t,P j i) (fun i=> ∑ j∈t,Q j i) v x:=by
     induction t using Finset.induction_on with
     | empty=> simp_rw [Finset.sum_empty]; exact nilA ..
     | insert i s hi ih=>simp_rw [Finset.sum_insert hi]; exact plusA (h i (mem_insert_self ..)) (ih (fun i hi=>h i (mem_insert_of_mem hi))) hx hp
lemma basisPad {X Y:M→Script I (d+2)}(h:Auger m X Y v x){A B:M→ Row I I} (hp:Silk σ A B v x)(hx:0<σ)(hX:1≤ x)(hv:0≤v): Auger m (fun i=>pad (A i) (X i)) (fun i=> pad (B i) (Y i)) v x:=by
     let Z(i:M):= pad (A i) (X i); let W(i:M):=pad (B i) (Y i); have h1:Loan m Z (1*1) x:= fuse_self hx hX zero_le_one hp.A h.A; have h2: Loan m W (1*1) x:=fuse_self hx hX zero_le_one hp.B h.B; rw [one_mul] at h1 h2; exact ⟨h1,h2,fuse_d hx hX hv hp.A hp.B h.A h.B hp.D h.D⟩
lemma basicCot {X Y:M→Script I (d+1)}(h:Auger m X Y v x){A B:M→ Row I I} (hp:Silk σ A B v x){T U:M→Script I (j+1)}(hT:Auger m T U v x)(hx:0<σ)(hX:1≤ x)(hv:0≤v): Auger m (fun i=>cotton (A i) (X i) (T i)) (fun i=> cotton (B i) (Y i) (U i)) v x:=by
     let Z(i:M):= cotton (A i) (X i) (T i); let W(i:M):=cotton (B i) (Y i) (U i); have h1:Loan m Z (1*1*1) x:= trellisTurn h.A hT.A hp.A hx zero_le_one hX; have h2: Loan m W (1*1*1) x:=trellisTurn h.B hT.B hp.B hx zero_le_one hX; rw [one_mul,one_mul] at h1 h2; exact ⟨h1,h2,loadedCot hx hX hv hp.A hp.B hp.D h.A h.B hT.A hT.B h.D hT.D⟩
end fares
end YM.OPE.Drift
