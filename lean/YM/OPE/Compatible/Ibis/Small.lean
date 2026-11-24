import YM.OPE.Compatible.Ibis.Hark
import YM.OPE.Compatible.Hull.Bevy
import YM.OPE.Compatible.Chest.Gable
/-! # stencil budgeting for ℓ² witnesses. peel support. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d:ℕ}{n:Side}{ε v s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
section
lemma swamp (b:ℕ) (x:Page (Shade G) i)(h:x∉encircled G b i): b+1 ≤ stamp x :=by
       by_contra! hh; have hx(p:Cover)(he: Laurent.size p ≤ b): p∈box b:=by
            have hz(i:Axis): (p i).natAbs ≤ Laurent.size p:=Finset.single_le_sum (f:=fun i=> (p i).natAbs) (fun (_:Axis) _=>Nat.zero_le _) (mem_univ i); rw [box_test]; exact ⟨fun i=> (by specialize hz i; omega),fun i=>(by specialize hz i; omega)⟩
       have hg(j:Fin i):∃ y:Fpaper G b,x j=pealB y:=by
            let p:Edge Cover:= ((x j).1,(x j).2.1); have ht:Laurent.size p.1+1 ≤ b:=by
                  rw [Page.perimeter] at hh; have hl:= Finset.single_le_sum (f:=fun j:Fin i=> Laurent.size ((x j).1)) (fun _ _=>Nat.zero_le _) (mem_univ j); change Laurent.size (x j).1+1≤b; omega
            have hu : Laurent.size (step p.2:Cover)=1:=by simp [Laurent.size,Lattice.step,Pi.single_apply,apply_ite (fun i:ℤ=>i.natAbs)]
            exact ⟨(⟨p, hx _ (by omega), hx _ ((size_add p.1 _).trans (hu ▸ ht))⟩,(x j).2.2),rfl⟩ -- proof hu ▸ direction
       choose q hq using hg; exact h (mem_image.mpr ⟨q,mem_univ _,(funext hq).symm⟩)
noncomputable abbrev Wfee_Z (m b:ℕ):ℝ:= (b+1:ℕ)^m
lemma Zγ (b m:ℕ):0<Wfee_Z m b:=by unfold Wfee_Z; positivity
noncomputable def StrandX (p:Curtain (Shade G))(b:ℕ):Curtain (Shade G):=fun i x=> if x∈encircled G b i then p i x else 0
lemma tide_m (p:Curtain (Shade G))(h:Volume p d m s)(b:ℕ): Volume (StrandX p b) d m s:=by
         refine ⟨fun i hi=>by funext x; unfold StrandX; rw[h.1 i hi];simp, fun i=>Sack.slim (h.2 i) (fun j=> (zero_le_one.trans (payer m j))) (fun j=>by unfold StrandX; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _)⟩
lemma billHi (p:Curtain (Shade G))(h:Volume p d (m+k) s)(b:ℕ): Volume (p-StrandX p b) d m ((Wfee_Z k b)⁻¹*s):=by
       have ht:=Zγ b k
       refine ⟨fun i hi=>by rw [Pi.sub_apply,h.1 i hi,(tide_m p h b).1 i hi,sub_zero],fun i=>?_⟩
       let B:= Wfee_Z k b; let g(x):= figure (m+k) x * ‖p i x‖; let V:= h.2 i; refine Work.F08.budget_minor (g:=fun i=>B⁻¹ *g i) (show SumBudget _ _ from ⟨fun x=>mul_nonneg (inv_nonneg.mpr ht.le) (V.1 x), V.2.1.mul_left _, (tsum_mul_left (f:=g)).trans_le (mul_le_mul_of_nonneg_left V.2.2 (inv_nonneg.mpr ht.le))⟩) (fun x=>mul_nonneg (zero_le_one.trans (payer m x)) (norm_nonneg _)) (fun x=>?_)
       by_cases hh:x∈encircled G b i
       · rw [show (p-StrandX p b) i x=p i x-StrandX p b i x from rfl,StrandX,if_pos hh,sub_self,norm_zero,mul_zero]; exact mul_nonneg (inv_nonneg.mpr ht.le) (V.1 x)
       rw [show (p-StrandX p b) i x=p i x-StrandX p b i x from rfl,StrandX,if_neg hh,sub_zero]; apply (le_inv_mul_iff₀ ht).2; unfold g; change B* _≤_;rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); rw [show figure (m+k) x=figure k x*figure m x from (show (stamp x:ℝ)^(m+k)= _ from (by rw[pow_add,mul_comm]; rfl))]; refine mul_le_mul_of_nonneg_right ?_ (zero_le_one.trans (payer m x)); exact pow_le_pow_left₀ (Nat.cast_nonneg _) (show (↑(b+1:ℕ):ℝ) ≤ ↑(stamp x) from by exact_mod_cast swamp b x hh) k
lemma totalU (p:Seat k m I)(h:Volume (lilies m k _ p) k m s): ‖p‖ ≤ s:=by
        let A:= fundus _ s h; have hx : A=p:= lilies_inj I k m (sproutsX _ h); exact (congr_arg norm hx.symm).trans_le (sproutsU _ h)
lemma safeC (p:Seat d m (Shade G))(b:ℕ)(h:Volume (lilies m d _ p) d (m+k) s): ∃ P∈Hoard G b d m, ‖P‖≤ s∧ ‖p-P‖ ≤ (Wfee_Z k b)⁻¹*s:=by
        let q:=lilies m d (Shade G) p; let P:=StrandX q b; let H:= tide_m q (VolumeWe h (Nat.le_add_right m k)) b; let p':=fundus P s H; have hh:=sproutsX P H; refine ⟨p',fun i x hx=> ?_,sproutsU P H,?_⟩
        · rw[show _= P from (show lilies m d _ p'= P from hh)]; unfold P StrandX; rw [if_neg hx]
        apply totalU; rw [map_sub,show lilies m _ _ p'=P from hh]; exact billHi q h b
end
end YM.OPE.Ibis
