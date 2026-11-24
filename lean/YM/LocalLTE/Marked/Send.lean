import YM.LocalLTE.Marked.Flint
import YM.MergeProof.Appl
/-! # Regular script for second unforced log. Keeps repeats. No Hessian subtraction yet!

Anchor on UNION site; pays factor exp surplus at endpoint, doesn't move
 each genealogy to fresh center. Keep honest clustered labels.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

namespace Captain
variable (N : Captain H j C' d v Y A b r B q k χ)
variable (p : Clusters H.ThinP)
open Greenbelt


open Merge Merge.Palette Height Daisy Lotus
-- every factor still selected independently.R.indices attached later. purposes geometry active.Down.
variable {ι:Type}[Fintype ι] (M:ι→Lotus.Leaf R)(rA:ι→ℝ)(he:∀ i, 0≤rA i)
set_option quotPrecheck false
local notation "χz"=> Merge.Palette.sign M S
local notation "τ"=> Merge.Tickets (Merge.Palette.sign M S)

-- bet costs on multiselects and draw routes. Prove zero off.R.
-- TERR Bayesian.

variable {V:Type}[DecidableEq V](S':Marker.Census V) (z:ι→Marker.Poly S')(ht:∀ i,z i*z i=0)
open Marker Switch
-- Vac scalar separated. polynomial.Y Φ. partition.
-- α DOES NOT INCLUDE Density normalized.F. weight marker dictionaries.RO.
def roll (i:Option (Fin p.fst))(D:Oscars M p) (U:Config G c): Ways ι:= Switch.click (D i).val ((∏ j∈(D i).val,rA j)*Palette.act M H χ U (p.snd i).val (D i))
def escort (i:Option (Fin p.fst))(W: Tickets χz) (U:Config G c): Ways ι:= click W.val ((∏ j∈W.val,rA j)*Palette.act M H χ U (p.snd i).val W)
def pulseV (D: Oscars M p): Marker.Poly S':= ∏ i,∏ j∈(D i).val,z j
-- local spin -- placeholder.F conflict!
-- `empty` excluded
omit [Fintype ι] in
lemma pressured (Q:Tickets χz)(D:Option (Fin p.fst))(U:Config G c)(a:ℝ)(P:Finset ι):
   escort (χ:=χ) p M rA D Q U a P=(∏ j∈Q.val,Palette.ways rA a P j)* Palette.act M H χ U (p.snd D).val Q:=by
     rw [Palette.amplitudes]; unfold escort click; split_ifs <;> ring
-- coset record

def handle (U:Config G c): Ways ι:= Palette.song M H χ rA p U
include ht
lemma horns (U:Config G c):
    Switch.sound z (handle (χ:=χ) p M rA U) = ∑ i:Oscars M p, (↑(pearl p M rA i*(coefficient H.seam p.2* (∏ j, Palette.act M H χ U (p.2 j).val (i j))/↑(p.fst+1).factorial)):ℂ) • pulseV p M S' z i:=by
    let V i v:= escort p M rA i v U (χ:=χ); let G i v (_:Unit):= V i v
    let F i w:= ‖(∏ j∈(w:Merge.Tickets χz).val,rA j)*Palette.act M H χ U (p.snd i).val w‖
    let f i:= ∑ v,V i v
    have h i v : Switch.Paid (G i v) (F i v):= paidClick _ (norm_nonneg _) fun _=> le_rfl
    let δ:= coefficient H.seam p.2/(p.fst+1).factorial; let g : Ways ι:= fun _ _=> δ
    have hf i : Switch.Paid (fun _:Unit=> f i) (∑ k,F i k):=by convert (Switch.Paid.sum univ (G i) (F i) (fun i _=> h ..)) using 1; funext _; simp [f,G]
    have hg:Paid (fun _:Unit=>g) ‖δ‖:= Switch.constant (fun _=>δ) (norm_nonneg _) (fun _=>le_rfl)
    have hu : handle (χ:=χ) p M rA U=g*∏ i,f i:=by
       ext a t; change coefficient H.seam p.2*(∏i:Option (Fin p.fst), Palette.color M H χ U (Palette.ways rA a t) (p.snd i).val)/↑(p.fst+1).factorial= δ*(∏ i,f i) a t
       have h i : Palette.color M H χ U (Palette.ways rA a t) (p.snd i).val=f i a t:=by unfold f; simp_rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro j _; exact (pressured p M rA _ _ U a t).symm
       simp_rw [Finset.prod_apply,h]; unfold δ; ring
 
    have hV : Paid (fun _:Unit=> ∏ i,f i) (∏ i:Option (Fin p.fst),∑ k,F i k):=by convert (Switch.Paid.prod univ (fun i (_:Unit)=>f i) _ (fun i _=>hf i)) using 1; funext _; rw [Finset.prod_apply]
    rw [hu,mul_sounds z ht (show Models g _ from (hg.works ()).choose_spec) (show Models (∏ i,f i) _ from (hV.works ()).choose_spec),const_sounds,Poly.product_bead,Switch.product z ht _ _ _ (fun i (_:i∈univ)=> hf i)]
    have hk i:sound z (f i) =∑ v,sound z (V i v):=Switch.summed z univ (V i) _ (fun i _=> h ..)
    simp_rw [hk]; rw [Fintype.prod_sum, Finset.smul_sum]; apply Finset.sum_congr rfl; intro D _
    let P i:= Palette.act M H χ U (p.snd i).val (D i); let q i:=∏j∈(D i).val,rA j
    have h i: sound z (V i (D i))=(↑(q i*P i):ℂ) • (∏ j∈(D i).val,z j):= Switch.gather ..
    simp_rw [h]; rw [Finset.prod_smul,smul_smul]; apply congr_arg (· • pulseV p M S' z (_:Oscars M p));

    rw [← Complex.ofReal_prod,← Complex.ofReal_mul]; apply congr_arg; unfold δ; rw [prod_mul_distrib]; unfold q P pearl; ring
end Captain
end YM.ConnectedActivityE6.Blaze.March
