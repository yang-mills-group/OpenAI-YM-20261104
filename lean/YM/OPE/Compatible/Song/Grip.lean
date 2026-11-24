import YM.OPE.Compatible.Song.Tan
/-!
# Rank layer shape.Main phase engagement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL
variable {i j d k m r l b:ℕ}{n:Side}
variable (hp:Board n (r+1)) (P T:Bid.Dir G n→ℝ)
open OrientX
-- assemble rank Δ.On.Plex.Per molecule. finite-sum proof without detection
private lemma rankSum {W E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (S:Finset W)(P:W→ E→ℝ)(x:E)(ht:∀ i∈S,ContDiff ℝ ω (P i)): Claw.rank (fun y=> ∑ i∈S,P i y) d x =∑ i∈S, Claw.rank (P i) d x:=by
       unfold Claw.rank; rw [show (fun y=> ∑ i∈S,P i y)=∑ i∈S,P i from funext fun j=> (Finset.sum_apply ..).symm,Tensor.coeff_sum d 0 P S (fun i hi=>(ht i hi).contDiffAt.of_le le_top)]; exact _root_.sum_apply .. -- ext syntax
set_option quotPrecheck false
local notation "FF"=>↥(fieldP r)
set_option maxHeartbeats 200000
private lemma rank_transport {D W : Type} [Fintype D] [Fintype W]
    (Z : Libra.Keys G D →ₗ[ℝ] Dual' (Libra.Keys G D))
    (F : Libra.Keys G W →L[ℝ] Libra.Keys G D) (L : Law (Libra.Keys G W))
    (R : Libra.Keys G D → ℝ) (x : Libra.Keys G D) (q : ℕ) :
    Z x (F (νrt Z F L R q x))=Claw.rank R (q+1) x-ρX Z F L R q x :=by
  simp only [νrt,ρX,Function.comp_apply]
  exact (OrientX.Crest (P:=L) (L:=Z) (F:=F) R x q).symm

lemma corona (L:Law (Chamber G r))(R:Bid.Dir G n→ℝ) (hx:ContDiffAt ℝ ω P 0)
       (Y:↥(fieldP r)→Bid.Dir G n→G.Color)
       (h:∀ j:↥(fieldP r),ContDiffAt ℝ ω (Y j) 0) (he:∀ j:↥(fieldP r),∀ i:G.ColorIndex, jet ((Phone G).coord i∘ (Y j)) d=(fun x=> (Phone G).coord i (νrt (chrom P) (sailT G hp) L R d x j))) (x:Bid.Dir G n) : Claw.rank (fun y=> (∑ i:↥(fieldP r), (Cake (sett n 0 i.val) false P T (Y i) d) y).s) (d+1) x=Claw.rank R (d+1) x-ρX (chrom P) (sailT G hp) L R d x:=by
  let p (i:FF) := Cake (sett n 0 i.val) false P T (Y i) d
  let A (i:FF) := fun y=>(p i y).s
  have component : (fun y:Bid.Dir G n=>(∑ i:FF,p i y).s)=(fun y=>∑ i,A i y) :=by
    funext y
    exact seqSum univ (fun i:↥(fieldP r)=>p i y) 0
  rw [component,rankSum univ A x (fun i _=>
    (ScriptJ.bondX (CakeB (sett n 0 i.val) false P T (Y i) d)).1.smooth)]
  let F:=sailT G hp
  let Z:=chrom P
  have hh:=rank_transport Z F L R x d
  rw [←hh]
  unfold A
  simp_rw [p,lightQ _ _ _ _ _ d hx (h _)]
  nth_rw 1 [resident (νrt Z F L R d x)]
  rw [map_sum,map_sum,Fintype.sum_prod_type]
  unfold topψ
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  rw [he,map_smul,map_smul]
  have hT:=splay hp P x j k hx
  have hz:=turnsT P (hx.of_le le_top) (F (PickL G (j,k))) x
  change _*_=_
  exact (congr_arg₂ (·*·) (hT.trans hz) rfl).trans (mul_comm ..)
end YM.OPE.Merchant
