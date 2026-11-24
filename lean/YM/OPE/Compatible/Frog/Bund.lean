import YM.OPE.Compatible.Frog.Kelp
/-!
# Euler normal. stabilization; true stance degree.
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
lemma bolts (A: Seat d (τ 0) (Shade G))(h:Aware d τ)(hp:A∈ bed G d (τ 0)): peakV G h A ∈ bed G (d+(2:Phase).val) (τ 2) :=by
      intro i; rw [peak_eq A h]; apply Submodule.smul_mem; let X:= lilies (τ 0) d (Shade G) A i; obtain ⟨hh,hy,H⟩:= merit hp i; change X∈_; exact ⟨⟨_,soot_le_k _ _ (sproutV (τ 0) d A|>.2 i) (ascLower h)⟩,hh,H,hy⟩
lemma scalarRam (b:ℝ)(h:Aware d τ)(p:T!)(hp:p∈solar G d τ): traceOf G b h p∈solar G d τ:=by
     let x:=p 0; let A:=peakV G h x; let v:= (b/2) • A; have hv:v∈ bed G (d+(2:Phase).val) (τ 2):=(bed G _ _).smul_mem _ (bolts x h (oak p hp 0 fun j hj=>False.elim (by revert j hj; decide))) -- not m
     let T:= crestL G h 2 ⟨v,hv⟩; rw [show traceOf G b h p=T.val from ?_]; exact T.property; ext1 i; rw [show traceOf G b h p= Pi.single 2 v from rfl]; by_cases he:i=2
     · subst i; exact (Pi.single_eq_same _ _).trans ((crestP G h 2 ⟨v,hv⟩).1.symm)
     have hx: i < (2:Phase):=by revert he;fin_cases i<;>decide
     rw [Pi.single_eq_of_ne he]; exact ((crestP G h _ _).2 i hx).symm
lemma aboard (b:ℝ)(h:Aware d τ)(p:T!)(hp:p ∈ solar G d τ): rebase G h b p∈ solar G d τ:=by unfold rebase; erw [_root_.add_apply]; exact (solar G d τ).add_mem hp (scalarRam b h p hp)
lemma successive (u v:ℝ)(p:T!)(h:Aware d τ): rebase G h u (rebase G h v p)= rebase G h (u+v) p:=by
     funext i; by_cases he:i=2
     · subst i; rw [sip,sip,sip,sail _ (0:Phase) _ _ (by decide), add_div, add_smul]; abel
     simp_rw [sail _ _ _ _ he]
lemma salute (p:T!)(h:Aware d τ):rebase G h 0 p=p:=by
     funext i; by_cases he:i=2; subst i; rw [sip]; simp; exact sail _ _ _ _ he
-- rebase effects on Mark
lemma crossR (p:T!)(h:Aware d τ)(b:ℝ)(x:Bid.Dir G n)(u:Site n) (i:Phase)(hp:i.val <2): (inkM (spread G d τ (rebase G h b p)) d u x).seq i.val=(inkM (spread G d τ p) d u x).seq i.val:=by
     rw [vein_i,vein_i]; suffices H: spread G d τ (rebase G h b p) i=spread G d τ p i from H ▸ rfl; exact congr_arg (lilies (τ i) (d+i.val) (Shade G)) (sail _ _ _ _ (show i≠2 by intro hx;subst i; contradiction)) -- hp omega
lemma flot (y:Tower (Shade G) d τ)(h:Aware d τ)(b:ℝ)(x:Bid.Dir G n)(u:Site n):
     let T:= inkM (spread G d τ y) d u
     inkM (spread G d τ (rebase G h b y)) d u x=T x+ ⟨0,0,(b/2)*deriv (fun i:ℝ=>(T (i • x)).s) 1⟩:=by
          intro T; apply JetS.eta
          · rw [JetS.pl_s,add_zero]; exact crossR _ _ _ _ _ 0 (by decide)
          · rw [JetS.pl_l,add_zero]; exact crossR _ _ _ _ _ 1 (by decide)
          let U:=spool G n; let P:=lilies (τ 0) d (Shade G); let Q:= lilies (τ 2) (d+(2:Phase).val) (Shade G); let p:= peakV G h (y 0); rw [JetS.pl_h]; change Flair (Q (rebase G h b y 2)) (d+(2:Phase).val) (U x) u= Flair (Q (y 2)) (d+(2:Phase).val) (U x) u+_
          rw [sip,map_add, flairA _ _ _ (Volume.bound _ (sproutV ..)) (Volume.bound _ (sproutV ..))]; congr 1; let v:= b/2; rw [show Flair (Q (v • p)) (d+(2:Phase).val) (U x) u=v* Flair (Q p) (d+(2:Phase).val) (U x) u from ?_]; swap; · unfold Flair;rw [map_smul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>score_scaled u _ _ v
          rw [show Q p=fun i:ℕ=>(i:ℝ) • (P (y 0)) i from funext fun i=> peak_eq (d:=d) (y 0) h i, nScore (P (y 0)) (sproutV ..) _ u _ (Nat.le_add_right ..)] -- rhs expo.J0
          congr! 2 with i
end YM.OPE.Drift
