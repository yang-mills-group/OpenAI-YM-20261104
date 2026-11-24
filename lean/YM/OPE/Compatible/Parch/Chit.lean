import YM.OPE.Compatible.Parch.Board
import YM.Work.F03.Transport
/-!
# Currents on one footprint. Cover and ANY contour.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw
variable {i j d k m r l b:ℕ}{n:Side}{S:Finset Cover}{o:Cover}
namespace Prom
variable (P:Prom S o m) (b:ℕ)
variable (hp:S⊆Lattice.box b)(hb:Board n b)
abbrev Tray (G:Gauge) (S:Finset Cover):= Libra.Keys G (↥(crossV S))
noncomputable def current (U:CoverConfig G):Tray G S:= fun i=> G.curvature (travel U o (P.ringL i))
noncomputable def brood (x:Tray G S):Tray G S:= P.current (lobK G S x)
lemma glow (s:Cover→ G.El)(V:CoverConfig G): P.current (Lattice.gauge s V)= glint _ (s o) (P.current V):=by funext i; unfold current; rw[travel_gauge, P.trip, G.curvature_conjugate];rfl
lemma hots (x:Bid.Dir G n)(i:Site n):P.brood (dip (fun i:↥(crossV S)=>i.val) n i x)=P.current (expandAt i (represent x)):=by funext q; unfold brood current; rw [P.coreK _ _ (glowQ x i)] -- orientation
lemma blurs (x:Bid.Dir G n) : P.brood (BlurD G (crossV S) n x)=P.current (expandAt 0 (represent x)):= hots P x 0
-- smooth proof all x
lemma matL (G:Gauge)(i:Edge Cover): ContDiff ℝ ω (fun x:Tray G S=> G.mat (lobK G S x i)):=by
       unfold lobK TipP; split
       next h=> exact G.exp_jet.comp (contDiff_apply ..)
       exact contDiff_const
lemma travelsB (G:Gauge)(x:Cover) (w:Walk) : ContDiff ℝ ω (fun z:Tray G S=>G.mat (travel (lobK G S z) x w)):=by
        induction w generalizing x with
        | nil=>exact contDiff_const
        | cons a w ih=>
             simp only[travel,G.mat_mul]; refine ContDiff.mul ?_ (ih _); unfold Step.read; split_ifs ; · simp only[G.mat_inv]; exact (starL' ℝ: G.Mat ≃L[ℝ] G.Mat).contDiff.comp (matL G _)
             exact matL ..
noncomputable def milk (G:Gauge): G.Mat →L[ℝ] G.Color:= (G.projectColor).toContinuousLinearMap ∘L ((1/2:ℝ) • ((ContinuousLinearMap.id ℝ G.Mat)-(starL' ℝ:G.Mat≃L[ℝ] G.Mat).toContinuousLinearMap))
lemma currentM (U: CoverConfig G)(x:↥(crossV S)):P.current U x=milk G (G.mat (travel U o (P.ringL x))):=by unfold current Gauge.curvature milk; rw[G.mat_inv];rfl
lemma bliss (G:Gauge):ContDiff ℝ ω (P.brood (G:=G)):=by refine contDiff_pi.mpr (fun i=>?_); unfold brood; simp_rw [currentM]; exact (milk G).contDiff.comp (travelsB G o (P.ringL i))
lemma travelAt (U:Config G n)(w:Walk):travel (expandAt 0 U) o w= travel U (wrap n o) w:=by rw[travel_at,add_zero]
noncomputable def signal (v:Bid.Dir G n)(x:↥S):G.Color:= Exterior.linkSum (Exterior.collect G v) (wrap n o) (P.voyage x)
lemma branchL (x:↥S)(v:Bid.Dir G n):HasDerivAt (fun t:ℝ=>G.mat (travel (expandAt 0 (represent (t • v))) o (P.voyage x))) (G.colorMat (P.signal v x)) 0:=by simp_rw [travelAt (n:=n)]; exact Push.travell ..
lemma link_ray (x:Edge Cover)(v:Bid.Dir G n):HasDerivAt (fun t:ℝ=>G.mat (expandAt 0 (represent (t • v)) x)) (G.colorMat (v (arkE (Moor x n)))) 0:=by simp only[expandAt,add_zero]; simp_rw [arkL]; exact Stationary.exp_ray ..
lemma ΩBill (x:↥(crossV S))(v:Bid.Dir G n):HasDerivAt (fun t:ℝ=> P.current (expandAt 0 (represent (t • v))) x) (P.signal v (firstB x)+v (arkE (Moor x.val n))- P.signal v (upperB x)) 0:=by
       unfold current; simp_rw [P.readC]; refine Work.F03.curvature_of_hasDerivAt ?_; simp only[G.mat_mul,G.mat_inv]; convert! ((P.branchL (firstB x) v).mul (link_ray x.val v)).mul ((P.branchL (upperB x) v).star) using 1
       have hs(w:Walk):travel (expandAt 0 (represent (0:Bid.Dir G n))) o w=1:=by rw [travelAt]; exact Push.stroll_zero ..
       simp only[zero_smul,Pi.mul_apply,hs,map_sub,map_add,G.mat_one,G.colorMat_skew]; simp [expandAt]; abel
include hp hb
lemma markJ (v:Bid.Dir G n): ∃ x: Site n→G.Color, HasDerivAt (fun t:ℝ=> P.brood (BlurD G (crossV S) n (t • v))) (BlurD G _ n (v+gillS (tor n) x)) 0:=by
       let M(i:Site n):G.Color:=if ht:lift i∈S then P.signal v ⟨_,ht⟩ else 0; have hv(x:↥S): M (wrap n x.val)=P.signal v x:=by
            unfold M; have he:lift (wrap n x.val) = x.val:=level hb (hp x.property); rw[dif_pos (he.symm ▸ x.property)]; congr
       refine ⟨M,hasDerivAt_pi.mpr fun i=>?_⟩; simp_rw [blurs]; have hh:=P.ΩBill i v; refine hh.congr_deriv ?_; rw [echoP,Pi.add_apply,GateV,← pier,show M (Moor i.val n).1=P.signal v _ from hv (firstB i),show M (wrap n (dotUp i.val))=P.signal v _ from hv (upperB i)]; abel
omit hp hb
lemma air (G:Gauge) : P.brood (0:Tray G S)=0:=by
       funext i; unfold brood current; have hx:lobK G S 0=1:=by funext j; unfold lobK TipP; split; simp; rfl
       rw[hx]; have ht(w:Walk)(p:Cover):travel (1:CoverConfig G) p w=1:=by induction w generalizing p with
                                                                           | nil=>rfl
                                                                           | cons i w ih=>rw [travel,ih]; unfold Step.read; split<;> simp
       rw[ht,G.curvature_unit]; rfl
end Prom
end YM.OPE.Merchant
