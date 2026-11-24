import YM.OPE.Compatible.Broma.Piece
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
variable {x v:M→ℝ}{σ C:ℝ}
lemma appVan {X:M→Script I r}(hx:Loan m X 1 x):Auger m X X v x:=⟨hx,hx,by rw [sub_self]; exact Loan.zero ..⟩
lemma auger_roll {X Y:M→Script I r}(h:Auger m X Y v x)(a:ℝ):Auger m (a • X) (a • Y) v x:=by refine ⟨h.A.scaleL _,h.B.scaleL _, ?_⟩; rw [← smul_sub]; exact h.D.scaleL _
lemma Wealthy (d r:ℕ)(j:Phase){P Q:M→Story I}{A B:M→Row I I}{X Y:M→Spring I}(hp:∀ j:Ask,Auger m (fun i=>Paloma (P i) j) (fun i=>Paloma (Q i) j) v x)(h:Silk σ A B v x)(hX:∀ i l,Auger m (fun j=> X j i l) (fun j=> Y j i l) v x)(hσ:0<σ)(ht:1 ≤ x)(hv:0 ≤ v):
    Auger m (fun i=> Mouth (A i) (P i) (X i) d j r) (fun i=>Mouth (B i) (Q i) (Y i) d j r) v x:=by
         unfold Mouth stretchH rootCush; simp_rw [Finset.sum_apply, Pi.smul_apply, Finset.sum_apply, Finset.smul_sum]; refine Aset _ _ univ ?_ ht hv; intro k _; apply Aset _ _ _ _ ht hv; intro y _; apply Aset _ _ _ _ ht hv; intro a _; apply Aset _ _ _ _ ht hv; intro u _; exact auger_roll (stamps (s:=a) (b:=fun _=>true) (e:=0) h hσ ht hv (auger_s (finCongr (Nat.zero_add u).symm) (hX k u)) hp) (Char.meter a)
lemma shuttle {A:M→Row I J}(hp:Tip σ A v x):Tip σ (fun i=>marry (A i)) v x:=by obtain ⟨a,c,q,h⟩:=hp; exact ⟨a,c,q,fun i j k=>h i j.2 k⟩
lemma cycleMar {A B:M→Row I J}(hp:Silk σ A B v x):Silk σ (fun i=>marry (A i)) (fun i=>marry (B i)) v x:=⟨shuttle hp.A,shuttle hp.B,shuttle hp.D⟩
lemma areRoot {A B:M→Row I I}(hp:Silk σ A B v x)(hx:0 ≤ v)(hy:1≤ x): Silk σ (fun i=>ROOT (I:=J) (A i)) (fun i=>ROOT (I:=J) (B i)) v x:=⟨tipRoot hp.A zero_le_one hy,tipRoot hp.B zero_le_one hy,roots_tipδ hp.D hx hy⟩
lemma augBour {X Y:M→ Script I r} (hx:Auger m X Y v x) :Auger m (fun i=>bouquet (X i)) (fun i=>bouquet (Y i)) v x:=by
      refine ⟨hx.A.twirl,hx.B.twirl,?_⟩; have hh:=hx.D.twirl; convert! hh using 1; ext1 i; exact (bouquetSub ..).symm -- names
lemma trope [Fintype J] {A B:M→ Cross n I J}(p:Silk σ A B v x) {X Y:M→Script I r}(h:Auger m X Y v x)(ht:∀ i,0< v i)(hs:1≤x)(hσ:0<σ):Auger m (fun i=>countermove (A i) 0 (X i)) (fun i=>countermove (B i) 0 (Y i)) v x:= by
     exact ⟨clay 0 p.A h.A hs hσ,clay 0 p.B h.B hs hσ,reachesC 0 p.A p.B p.D h.A h.B h.D hσ hs ht⟩
end fares
end YM.OPE.Drift
