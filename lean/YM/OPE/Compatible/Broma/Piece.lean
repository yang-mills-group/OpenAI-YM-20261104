import YM.OPE.Compatible.Broma.Dale
/-!
# Dual Tau billing at all orders. linked push
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose
variable {n c f:Side}{I J M:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
section fares
variable {x p v:M→ℝ} {X Y:M→Script I (e+d)} {σ C:ℝ} [DecidableEq J]
variable {A B:M→Row I I} {s:Finset J}{D D': J→ℕ}{b:J→Bool}{Q Q':∀ _:M,∀ t:J,Script I (D' t+D t)}
local notation "L(" T "," Q "," i "," p ")"=> Shell.Hall (T i) D D' (Q i) b p
lemma stamps (hp:Silk σ A B v x)(hx:0<σ)(hX:1≤x)(hv:0≤v)(hr:Auger m X Y v x)(hh:∀ i:J, Auger m (fun t=>Q t i) (fun t=>Q' t i) v x):
    Auger m (fun i=> L(A,Q,i,s) d e (X i) r) (fun i=> L(B,Q',i,s) d e (Y i) r) v x:=by
         let T (s :Finset J)(d e:ℕ):Prop:=∀ X Y:M→Script I (e+d),Auger m X Y v x→ Auger m (fun i=>Shell.Hall (A i) D D' (Q i) b s d e (X i) r) (fun i=>Shell.Hall (B i) D D' (Q' i) b s d e (Y i) r) v x
         refine inductS T ?_ ?_ s d e X Y hr
         · intro w e P Q he; simp_rw [Hall_nil]; by_cases H:w=∅; swap;· simp_rw [if_neg H];exact nilA ..
           simp_rw [if_pos H]; by_cases ht:r=e; subst e; unfold Shell.throw; simp only [Pi.single_eq_same]; exact he; simp_rw [hubbub ht]; exact nilA .. -- wrong map
         intro t d e h ih hk X Y hr; simp_rw [script_run, Pi.add_apply, Finset.sum_apply]
         have he:= h (fun i=>Shell.Temper _ _ (X i)) (fun i=>Shell.Temper _ _ (Y i)) (auger_s (beginC e d) hr)
         have hd: Auger m (fun i=> WalkK (A i) e d (X i) (Shell.Hall (A i) D D' (Q i) b t) r) (fun i=>WalkK (B i) e d (Y i) (Shell.Hall (B i) D D' (Q' i) b t) r) v x:=by
              cases d with
              | zero=> simp_rw [soak_nil]; exact nilA ..
              | succ d=> simp_rw [soak_plus, Finset.sum_apply]; apply Aset _ _ _ _ hX hv; intro i _; apply ih d (Nat.lt_succ_self _) e; exact basisPad (auger_s (Equiv.Perm.decomposeFin.symm (0,wand e d i)) hr) hp hx hX hv
         apply plusA (plusA he hd hX hv) _ hX hv; apply Aset _ _ _ ?_ hX hv; intro i hi; by_cases he:b i=false
         · simp_rw [he,Bool.false_eq_true, if_false]; exact nilA ..
         simp_rw [Bool.eq_true_of_not_eq_false he,if_true]; have hv'(k:ℕ)(P P':M→Script I (D' i+k))(h:Auger m P P' v x): Auger m (fun j=>Once (A j) (Shell.Hall (A j) D D' (Q j) b (Finset.erase t i)) e d (X j) (D' i) k (P j) r) (fun j=>Once (B j) (Shell.Hall (B j) D D' (Q' j) b (Finset.erase t i)) e d (Y j) (D' i) k (P' j) r) v x:=by
              cases k with
              | zero=> exact nilA x v I r m
              | succ k=>
                   simp_rw [once_plus,Finset.sum_apply]; apply Aset _ _ _ _ hX hv; intro j _; exact hk _ hi _ _ _ _ (auger_s (Shell.plank e d (D' i) k) (basicCot hr hp (auger_s (wand (D' i) k j) h) hx hX hv))
         exact hv' (D i) _ _ (hh i)
end fares
end YM.OPE.Drift
