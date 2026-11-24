import YM.OPE.Compatible.Channel.Bonds
/-!
# Installed kernel representation in absolute page costs. Pin after, give exact finite-torus latitude.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Work.F08 Matrix
open scoped Topology BigOperators Classical
variable {r n:ℕ} {I J T:Type*}[Fintype T][Fintype I] {L c f:Side} {g:Ratio c f}{A:Cross g.count T I}{η U s:ℝ}
namespace Script
open Page
omit [Fintype T]
lemma bridge_torque (H: Whole A)(x:Site c)(w:Cover)(p: Script T r) (h: Summable p)(q: Fin r→deck I c) : scribe x (countermove A w p) q=scribe (g.embed x+wrap f w) p (fun i=> installed g A *ᵥ q i) := by
   have hs:Sack (figure 0) p (∑' i, ‖p i‖):= by unfold Sack figure poise; simp only [pow_zero,one_mul]; exact ⟨fun _=>norm_nonneg _,h.norm,le_rfl⟩
   obtain ⟨σ,C,hc,hP⟩:=H
   rw [valueFlow hP hc _ _ hs]; exact tsum_congr fun i=> congr_arg (p i * ·) (capstone i w ⟨_,_,hc,hP⟩ q x)
def payVolume (A:Cross L T I)(p: Script T r): Script I r:= ∑ i:Site L,silt (countermove A (lift i) p)
lemma volume_torque (H: Whole A) (p: Script T r) (h: Summable p)(q: Fin r→deck I c) : library c (payVolume A p) q=library f p (fun i=> installed g A *ᵥ q i) := by
   have hs:Sack (figure 0) p (∑' i, ‖p i‖):= by unfold Sack figure poise; simp only [pow_zero,one_mul]; exact ⟨fun _=>norm_nonneg _,h.norm,le_rfl⟩
   obtain ⟨σ,C,hc,hP⟩:= H; let F(i:Site g.count):=countermove A (lift i) p; have ht (i:Site g.count):= counterflow hP hc p (lift i) hs
   let u:= fun i=> installed g A *ᵥ q i; let G(i:Site f):= scribe i p u; let V:= g.assemble
   calc
      _ = ∑ y:Site c,∑ i:Site g.count,scribe y (silt (F i)) q:= Finset.sum_congr rfl fun i _=> reads_sum _ _ (fun j _=>sootS (silt_cost (ht j))) _ i
      _ = ∑ i:Site g.count,library c (F i) q:= Finset.sum_comm.trans (Finset.sum_congr rfl (fun i _=> (silt_read (p:=F i) (sootS (ht i)) q).symm))
      _ = ∑ y:Site c × Site g.count, G (g.assemble y):= by rw [Fintype.sum_prod_type, sum_comm]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; exact bridge_torque ⟨_,_,hc,hP⟩ j (lift i) p h q
      _ = _:= Equiv.sum_comp g.splitSites.symm G
-- torque uses exact EVERY period (regardless ratio offsets) for block linear invariant sources. -> canonical in normal flags.
end Script
end YM.OPE.Flume
