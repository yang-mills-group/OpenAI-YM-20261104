import YM.OPE.Compatible.Limn.Sound
/-!
# Boots in weighted gram. Dot arcs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}{X Y V:Type}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma
variable {t r R B b ε:ℝ}{m:ℕ}
variable {S:StepData c f}{F:Forest S.ratio} {I:Seats F}
open Finset Module
open Green (wt)
section
variable [Fintype X] [Fintype Y][Fintype V] (u:X↪Y) (v:Y↪X){p:X→Site f}{q:V→Site f}{C:Matrix X V ℝ}
omit [Fintype V] in
lemma farm_e {X':Type}[Fintype X'] (u:X'↪Key F G)(ht:0<t)(i:Site f) : (∑ j:X',Wisps.rate (-t) (separation i (pointK S F (u j))))≤ farm G t:=by
       apply le_trans _ (farmPay S F ht i); rw [← Finset.sum_map _ u (fun x=> Wisps.rate (-t) (separation i (pointK S F x)))]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> (Wisps.rate_pos ..).le -- find f name
lemma Han (h:Pours C p q t R): Pours (C.submatrix v id) (p∘v) q t R:=by
       constructor
       · exact h.pos
       · exact fun i=> h.row _
       intro j; change ∑ i:Y, Wisps.rate t (separation (p (v i)) (q j))*|C (v i) j| ≤ _; apply le_trans _ (h.col j); rw [← Finset.sum_map _ _ (fun i:X=> Wisps.rate t (separation (p i) (q j))*|C i j|)]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> mul_nonneg (Wisps.rate_pos ..).le (abs_nonneg _)
lemma Chan (h:Pours C p q t R)(i:X)(j:V): wt t (p i) (q j) * |C i j|≤ R:= le_trans (single_le_sum (s:=univ) (a:=j) (f:=fun j=>Wisps.rate t (separation (p i) (q j))*|C i j|) (fun _ _=>mul_nonneg (Wisps.rate_pos ..).le (abs_nonneg _)) (mem_univ j)) (h.row i)
end
local notation "A!"=> Key F G
section
variable (A:Matrix (Key F G) (Key F G) ℝ)(I:Seats F)
abbrev porchPrice (G:Gauge)(t R B:ℝ):ℝ:= (max (farm G (t/2)) (farm G (t/2))*B)*R
lemma torque (ht:0<t)(hB:0 ≤ B)(hp:Pours A (pointK S F) (pointK S F) t R)(C:∀ (i j:Rubric G I), wt t (pointK S F (shout G I i)) (pointK S F (shout G I j))*|(plateK S F I A)⁻¹ i j| ≤ B): Pours (clipRail S F I A) (pointK S F ∘ shout G I) (pointK S F) (t/2) (porchPrice G t R B):=by
       apply Pours.fuse _ (Han (shout G I) (hp.weaker (half_le_self ht.le) le_rfl)) (half_pos ht).le; exact Schur.pure ht hB C (farm_e (shout G I) (half_pos ht)) (farm_e (shout G I) (half_pos ht))
end
end YM.OPE.Limn
