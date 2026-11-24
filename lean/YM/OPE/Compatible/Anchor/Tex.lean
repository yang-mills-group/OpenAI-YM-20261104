import YM.OPE.Compatible.Anchor.Window
/-! # template field. Equivariant -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M E F:Type}{n:Side}
local notation "Y!" => Bid.Dir G n
local notation "Q!"=>CoverConfig G
lemma projectionExists [AddCommGroup E][Module ℝ E](L:(I→ℝ)→ₗ[ℝ] E)(h:Realm L):∃ s:Finset I,∃ v:(↥s → ℝ)→ₗ[ℝ] E,∀ w,L w=v (fun i=>w i.val):=by
    obtain ⟨s,H⟩:=h; let T:(↥s→ℝ)→ₗ[ℝ] (I→ℝ) := LinearMap.pi fun i:I=> if h:i∈s then LinearMap.proj (φ:=fun _:↥s=>ℝ) (⟨i,h⟩:↥s) else 0; exact ⟨s,L ∘ₗ T,fun w=>H _ _ (fun i hi=> (show w i= T _ i from (by unfold T; simp only[LinearMap.pi_apply,dif_pos (show i∈s from hi)];rfl)))⟩
noncomputable abbrev Motif (k:ℕ)(V:Q!):= templateX G k (board V)
lemma MotifLit (G:Gauge)(k:ℕ): Sensed (Motif k (G:=G)):=by
     let T:=templateX G k; obtain ⟨s,v,H⟩:= projectionExists T realmBase; let L:(↥s→ℝ)→L[ℝ] Taylor G k:=v.toContinuousLinearMap; let p(i:↥s)(x:CoverConfig G):= board x i.val; rw [show Motif k (G:=G)= L ∘ (fun x:CoverConfig G=>fun j:↥s=>p j x) from funext fun _=>H _]; have hL:ContDiff ℝ ω L := (by apply ContinuousLinearMap.contDiff); exact (candles p (fun i=>boardSeen i.val)).chain _ hL
lemma MotifCast (w:Cover→G.El)(V:Q!)(k:ℕ): Motif k (Lattice.gauge w V)= Taylor.paint (w 0) (Motif k V):=by unfold Motif; rw [boardGauge,color_template]
lemma tripOne (G:Gauge)(x:Cover)(w:Walk): travel (1:CoverConfig G) x w=1:=by induction w generalizing x with| nil=>rfl| cons a v ih=> simp [travel,ih,Step.read]
lemma MotifZero (k:ℕ): Motif k (G:=G) 1=0:=by unfold Motif; rw [show board (1:Q!)=0 from ?_,map_zero]; funext i; unfold board; rw [tripOne,G.curvature_unit];rfl -- names
lemma MotifGo (k:ℕ)(w:fieldX (Shade G)):HasDerivAt (fun t:ℝ=> Motif k (lotU (t • w))) (templateX G k w) 0:=by
      let f:=templateX G k; obtain ⟨s,v,h⟩:= projectionExists f realmBase; let L:(↥s→ℝ)→L[ℝ] Taylor G k:=v.toContinuousLinearMap; let D:=w + mountain (fun j=> (-bandC w j.1) j.2); let g (t:ℝ):= board (lotU (t • w)); let Gs(t:ℝ)(i:↥s):ℝ:=g t i.val
      rw [show (fun t:ℝ=> Motif k (lotU (t • w)))= L ∘ Gs from funext fun i=>h _, show templateX G k w= L (fun i:↥s=> D i.val) from ?_]; swap
      · have hv:templateX G k D=f w:=by unfold D; rw [map_add,temp_zero,add_zero]
        exact hv.symm.trans (h _)
      have h':HasDerivAt Gs (fun i=> D i.val) 0:=hasDerivAt_pi.mpr (fun i=>arcRead w _); apply HasFDerivAt.comp_hasDerivAt (l':=L) (l:=L) 0 _ h'; exact L.hasFDerivAt
lemma vacant_t (G:Gauge)(x:fieldX (Shade G)): lotU ((0:ℝ) • x)= (1:CoverConfig G):=by funext i; unfold lotU; rw [show indexS _ _=(0:G.Color) from (by rw [zero_smul]; rfl),G.mat_lieExp_zero];rfl
end YM.OPE.Variance
