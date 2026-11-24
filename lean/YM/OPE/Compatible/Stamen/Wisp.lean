import YM.OPE.Compatible.Stamen.Cuff
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
variable (W:Aware d τ)(u:Phase)
local notation "S!"=>Seat (d+u.val) (τ u) (Shade H)
section Baby
variable (p:Seat (d+u.val) (τ u) (Shade H))
local notation "B"=> lilies (τ u) (d+u.val) (Shade H)
abbrev plantV(i:Fin (d+u.val+1)):=glide (Grid.lance (lilies (τ u) (d+u.val) _ p i.val)) u
local notation "C!"=> empa H.ColorIndex (d+u.val) (τ u)
include W
lemma curbH (hp:p∈ empa H.ColorIndex (d+u.val) (τ u)) (i:Fin (d+u.val+1)):∃ a:ℝ,Tide (plantV u p i) d 0 a:=by
        obtain ⟨c,h⟩:= (show ∃ c:Phase→ℝ,∀ j:Phase,Volume (plantV u p i j) (d+j.val) 0 (c j) from (by choose a ha Ht using fun j:Phase=>burst (G:=H) W u i j; exact ⟨fun j=> a j*‖p‖,fun j=>VolumeWe (Ht j (B p i.val) ‖p‖ (hp.1 _) (hp.2 _) ((sproutV _ _ p).2 _)) (Nat.zero_le _)⟩)); have hv(j):0≤c j:= Sack.coins ((h j).2 0); refine ⟨∑ i,c i,fun i=>?_⟩; exact (h i).raise _ le_rfl (single_le_sum (fun i _=>hv i) (mem_univ _))
lemma landsB (z:Bid.Dir H N)(hp:p∈ empa H.ColorIndex (d+u.val) (τ u)):
       inkM (baby u p) d x z=Ū^u.val* ∑ i:Fin (d+u.val+1), inkM (Grid.lance ((lilies (τ u) (d+u.val) _ p) i.val)) (d+u.val) x z:=by
             choose a ha using fun i=>curbH W u p hp i; unfold baby; rw [inkify z Finset.univ _ a (fun i _=>ha i) x,Finset.mul_sum]; exact sum_congr rfl fun _ _=> baton ..
lemma rallyP (z:Bid.Dir H N)(hp:p∈ empa H.ColorIndex (d+u.val) (τ u)):
       let w:= charW x z; inkM (baby u p) d x z=Ū^u.val * (⟨Worth (m:=τ u) p w,PenD (m:=τ u) p w (mores w 2), PenD (m:=τ u) p w (mores w 3)+(2:ℝ)⁻¹* PenD2 (m:=τ u) p w (mores w 2)⟩:Token):= by
             intro w; rw [landsB x W u p z hp]; apply congr_arg; exact tokenRich x z _ hp (by have h:=W.credit u; have hz:=u.isLt;omega)
end Baby
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (Z:E→L[ℝ] Vec H N 1)[MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure] (A:Law E)
abbrev radiusV (p:Seat (d+u.val) (τ u) (Shade H))(t:E):= inkM (baby u p) d x ((flats H N).symm (Z t))
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in lemma climbsF (t:E): charW x ((flats H N).symm (Z t))=Charu x Z t:=by
       unfold charW Charu; congr 1; let f:=(flats H N).symm (Z t); refine (show spool H N _ = _ from ?_); rw [←(flats H N).apply_symm_apply (Z t)]; -- issue rewrites lhs; 
       rw[ContinuousLinearEquiv.symm_apply_apply]; exact ((spool H N).apply_symm_apply _).trans (congr_arg _ ((flats H N).apply_symm_apply _).symm) -- tweak
variable (r':Train r)(h:4 ≤ r)(C:KernelChoices)(p:Seat (d+u.val) (τ u) (Shade H))
-- ℓ shipments
include W in
lemma cloakBaby (ht:Licence Z A r' C)(hp:p∈ empa H.ColorIndex (d+u.val) (τ u))(he:Deep (m:=τ u) p (j+3*(2-u.val))) : MoldH A μ j (radiusV x u Z (Aγ r' h C (N:=N) (m:=τ u) p)):=by
       let Q:= Aγ r' h C (N:=N) (m:=τ u) p; have hq : Q∈ empa H.ColorIndex (d+u.val) (τ u):= writ _ hp _; let v:=Charu x Z; let F(i:E):= PenD (m:=τ u) Q (v i) (mores (v i) 2); let G(i:E):=Worth (m:=τ u) Q (v i); let R(i:E):= PenD (m:=τ u) Q (v i) (mores (v i) 3); let S(i:E):= PenD2 (m:=τ u) Q (v i) (mores (v i) 2)
       have hg0 : Husk μ A (j+3*(2-u.val)) G:= AuroraV x Z μ A r' h C p (by have h:=W.credit u;omega) ht hp he
       have hh (hv:u.val<2): Husk μ A (j+3*(1-u.val)) F:= fancy x Z μ A r' h C p _ (by have h:=W.credit u;omega) (by have h:=W.credit u;omega) (by omega) ht hp he
       have hs (hx:u.val=0): Husk μ A j (R + (2:ℝ)⁻¹ • S):= by
            have hv:Husk μ A j R:= fancy x Z μ A r' h C p _ (by have h:=W.credit u;omega) (by have h:=W.credit u;omega) (by omega) ht hp he; apply hv.split
            exact Husk.elementary (stormT x Z μ A r' h C p (by have h:=W.credit u;omega) ht hp (by rwa [show j+6=j+3*(2-u.val) from by rw[hx]])) _
       have hy(w:E): radiusV x u Z Q w= Ū^u.val * (⟨G w,F w,(R+(2:ℝ)⁻¹ • S) w⟩:Token):=by rw[radiusV, rallyP x W u Q _ hq,climbsF]; rfl
       intro a; change Husk μ A _ (skry (radiusV x u Z Q) a); rw[funext hy]; -- simplify T
       exact Mote μ A u a G F (R+(2:ℝ)⁻¹ • S) hg0 hh hs
where Mote (μ:Measure E)[μ.IsAddHaarMeasure](A:Law E)(u a:Fin 3)(G F R:E→ℝ)(hg:Husk μ A (j+3*(2-u.val)) G)(hh:u.val<2→ Husk μ A (j+3*(1-u.val)) F)(hR:u.val=0 → Husk μ A j R): Husk μ A (j+3*(2-a.val)) (skry (fun i=>Ū^u.val*(⟨G i,F i,R i⟩:Token)) a):=by
        fin_cases u <;> fin_cases a<;> unfold skry <;> simp [JetS.seq,Ū,pow_succ] at *; all_goals first| assumption| exact (show _ from trivialCost μ A)
end
end YM.OPE.Silt.Phere
