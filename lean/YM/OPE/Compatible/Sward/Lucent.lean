import YM.OPE.Compatible.Sward.Lux
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
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
section deg
variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
abbrev Breeze (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](j d:ℕ): Submodule ℝ (E→ℝ) where
       carrier:= {p| anthem d p∧∀ i:ℕ,i < j→ Tensor.coeff p i 0=0}
       zero_mem':=⟨anthem.bank _ _,fun i _=> Tensor.coeff_zero ..⟩
       add_mem':=fun {p q} ⟨h,hp⟩ ⟨ht,hq⟩=>⟨h.add ht, fun i hi=>by rw [Tensor.coeff_add ((h.cost.smooth.of_le le_top).contDiffAt) ((ht.cost.smooth.of_le le_top).contDiffAt),hp i hi,hq i hi,zero_add]⟩
       smul_mem':=fun a b (hx:anthem d b∧∀ i:ℕ,i < j→ _)=>⟨hx.1.scale _,fun i hi=>by erw [Tensor.coeff_smul a (hx.1.cost.smooth.of_le le_top|>.contDiffAt),hx.2 i hi, smul_zero]⟩
lemma sweepC {L:Filter I}[L.NeBot](f:I→E→ℝ)(v:E→ℝ)(h:∀ x:E,Tendsto (fun i=> f i x) L (𝓝 (v x)))(hq:∀ᶠ i in L,f i∈ Breeze E j d): v∈Breeze E j d:=by
        let U:= Breeze E j d; haveI:FiniteDimensional ℝ U:=hymn U (k:=d) fun i hi=>hi.1; exact U.closed_of_finiteDimensional.mem_of_tendsto (tendsto_pi_nhds.mpr h) hq
variable [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure](A:Law E)
lemma GradeUp (f:E→ℝ)(h:anthem k f): anthem k (Dawn μ A f):= gains μ A (fun v:E×E=> f (v.2+v.1)) (h.compLinear (LinearMap.snd ℝ E E + LinearMap.fst ℝ E E))
section
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F] (L:F→L[ℝ] E)
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ F] in
lemma onceD (f:E→ℝ)(h:Bond f)(k:ℕ)(a: Fin k→F): Tensor.coeff (f ∘ L) k 0 a=Tensor.coeff f k 0 (L ∘ a):=by
       unfold Tensor.coeff; rw [L.iteratedFDeriv_comp_right h.smooth 0 le_top,map_zero];rfl
lemma Duration (f:E→ℝ)(h:Husk μ A j f)(hp:anthem k f): (Dawn μ A f) ∘ L.toLinearMap ∈ Breeze F j k:=by -- fix composition parse
      let g:= Dawn μ A f; have ht: anthem k g:=GradeUp μ A f hp; refine ⟨ht.compLinear _,fun i hi=>?_⟩; ext a; change Tensor.coeff (g ∘ L) i 0 a= _; rw[onceD L g ht.cost i a,show Tensor.coeff g i 0= 0 from (prior μ A hp.cost).1 h i hi];rfl
end
end deg
open Matrix
lemma turfy (A:RowB I)(p:Seat k m I) (b:ℝ)(h:settled (m:=m) p): settled (m:=m) (boostS A b m k p):=by
        let S:Submodule ℝ (Seat k m I):={ carrier:= {p| settled (m:=m) p},zero_mem':=fun j=> by rw[map_zero]; exact fun _=>rfl,add_mem':=fun {p q} (h:settled (m:=m) p)(hp:settled (m:=m) q) j=>by rw[map_add,Pi.add_apply]; exact fun i=> congr_arg₂ (fun (a b:Script I j)=>a+b) (h j i) (hp j i), smul_mem':=fun a p (hp:settled (m:=m) p) j=>by rw[map_smul,Pi.smul_apply]; exact fun i=>congr_arg (fun t:Script I j=>a • t) (hp j i) }
        let D:= (lapD A m k).toLinearMap; have he(i:ℕ): (D^i) p∈S:=by induction i with | zero=> simpa|succ i ih=> rw[pow_succ',End.mul_apply]; exact tor_fit _ _ ih
        change boostS A b m k p∈S; rw [boostS,Hflow]; exact S.sum_mem fun i _=>S.smul_mem _ (he _)
abbrev LightP (p:Seat k m (Shade H)):= fun v:Bid.Dir H N=> Flair (lilies m k (Shade H) p) k (spool H N v) x
-- incoming any x
lemma polW (p:Seat k m (Shade H)): anthem k (LightP x (m:=m) p):=by
        let S:=formSong m k H x p; rw [show LightP x (m:=m) p= Strike k S ∘ (flats H N) from funext fun i=>(strikesT p x i).symm]; exact (sailCost S k).compLinear (flats H N).toLinearMap
lemma wellD (p:Seat k m (Shade H)) (v:Train r)(h:4 ≤ r)(hp:settled (m:=m) p):
       let B:= rentV H v h L N; let A:=Vessel L v H N h; let mθ:=Chart.tangent H (Exterior.Body 1 N)
       Dawn mθ A (LightP x (m:=m) p)=LightP x (m:=m) (boostS B (1/2) m k p):=by
            intro B A mθ; let S:= formSong m k H x p; let g:=flats H N; rw[show LightP x (m:=m) p= Strike k S∘ g.toContinuousLinearMap from funext fun i=> (strikesT p x i).symm,under mθ A g.toContinuousLinearMap S (chic x p hp), show chamber A g.toContinuousLinearMap= CapeV L H v N from (Hport L v H N h).choose_spec.1 ]; ext1 i; rw [show LightP x (m:=m) _ i= _ from (strikesT (boostS B (1/2) m k p) x i).symm, flareU (L:=L)]; rfl
end YM.OPE.Silt.Phere
