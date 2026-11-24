import YM.FormalBulk08.Turner.Walk

/-! Exact re-fibration at each finite mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Turner
open Series Wick Jets Orb Matrix Filter Set Function PowerSeries
open Stationary hiding Rays
open Lattice RG Precision Reef Work.F05 Tree MeasureTheory Wilson
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f}{F T: Forest S.ratio} {R: ChartRatio G}
open YM.AnalyticNext.QuarticMatch.Joint hiding power
open Flat
variable (e:F.Free≃ T.Free) (k:S.Choices)(R:ChartRatio G)
variable (hp:S.patch.Branches S.kernel G)(p:LocalRatio R)(L:Hull (Pine G S F) (wire G c))(Q:Hull (Pine G S T) (wire G c))(W:Pap (wire G f))
variable (he:Rite W W 1 0)
include he p hp
lemma summered :
   let z:= motor (spins G c); let D:= porch (pulse e) Q; let Y:= motor (track (G:=G) e)
   ∃ M: Matrix (Pine G S F) (Pine G S F) ℝ, Elan L D (flush F k R W) (abroad (pulse e) (flush T k R W)) z z (centered L D Y z z) (MvPolynomial.C.mapMatrix (dollars (track e) 0)) (MvPolynomial.C.mapMatrix M) := by
   intro z D Y; obtain ⟨M,hm,hM⟩:=brush e p
   refine ⟨M,comparison L D _ _ _ _ _ _ _ hm (inlay _) ?_⟩
   dsimp only [flush,vacuumU]; unfold z Y; simp_rw [map_add,_root_.map_sub]
   have h:= wing_view e W he; rw [caliber _ (track_zero e) ((slick e).of_le le_top) M hm (sap F R) (sap F R) (sap_smooth _ _ p) (sap_smooth _ _ p) (sap_root _ _ p) (sap_root _ _ p) z z hM,weekend e R p,noise_view e k hp]; unfold Reef.seat at h; rw [h]; unfold z;abel
omit p hp he
lemma spiny (p:Pap (wire G c)): roam ℝ (motor (spins G c)) p=p := by rw [show motor (spins G c)=fun i=> C (MvPolynomial.X i) from funext (motor_wires (I:=wire G c) id)]; exact virgin p
include e he p hp
lemma summer_vac (h:Solved L (flush F k R W))(hz:Solved Q (flush T k R W)): out L (flush F k R W)=out Q (flush T k R W) := by
    obtain ⟨M,E⟩:=summered e k R hp p L Q W he
    have ht:= action_view _ _ _ _ h (packed (pulse e) Q _ hz) _ _ _ _ _ E; rw [spiny,spiny] at ht; simp_rw [out,pounds _ _ _ hz] at ht; exact ht
lemma summer_fren (Z:Pap (wire G f))(hZ:Rite Z Z 1 0)(h:Solved L (flush F k R W))(hz:Solved Q (flush T k R W)): flag L (flush F k R W) (Reef.seat F Z)=flag Q (flush T k R W) (Reef.seat T Z):= by
    obtain ⟨M,E⟩:=summered e k R hp p L Q W he
    have hp:= (mark_view _ _ _ _ h (packed (pulse e) Q _ hz) _ _ _ _ _ E (Reef.seat F Z) (abroad (pulse e) (Reef.seat T Z)) (by rw [←lease, discount,wing_view e Z hZ])); rw [spiny,spiny,posed _ _ _ hz] at hp;exact hp
section
open Next.Free
variable {i j:ℕ}{K:KernelChoices}
omit he hp e p
lemma span_paths (R:ChartRatio G) (P:Flight j i)(h:P.patch.Branches K G)(F T: Lodge P.patch)(u v:(primary P.patch K c).Choices)(W: Pap (wire G (c*P.patch.L))) (p:LocalRatio R)(ht:4 ≤ i)(hz: coeff 0 W=crunch (kernelP G K.penalty P.wing _))(hp : Rite W W 1 0): landed P R h F c u W=landed P R h T c v W := by
     rw [landed_choice P R h T c v u]; exact summer_vac (freeEquiv _ _) u R h p _ _ W hp (consolidate P R h F c p u W hz ht) (consolidate P R h T c p u W hz ht)
lemma tossed_choice (R:ChartRatio G)(P:Flight j i)(h:P.patch.Branches K G)(F:Lodge P.patch)(u v:(primary P.patch K c).Choices)(W Y: Pap (wire G (c*P.patch.L))):tossed P R h F c u W Y=tossed P R h F c v W Y:= by unfold tossed; simp_rw [flush,vacuumU,clash (primary P.patch K c) h u v]
lemma tossed_paths (P:Flight j i)(h:P.patch.Branches K G)(F T:Lodge P.patch)(u v:(primary P.patch K c).Choices)(W Y:Pap (wire G (c*P.patch.L)))(p:LocalRatio R)(ht:4 ≤ i)(hz: coeff 0 W=crunch (kernelP G K.penalty P.wing _))(hp:Rite W W 1 0)(hy:Rite Y Y 1 0): tossed P R h F c u W Y=tossed P R h T c v W Y := by
     rw [tossed_choice R P h T v u]; exact summer_fren (freeEquiv _ _) u R h p _ _ W hp Y hy (consolidate P R h F c p u W hz ht) (consolidate P R h T c p u W hz ht)
end
end YM.FormalBulk08.Turner
