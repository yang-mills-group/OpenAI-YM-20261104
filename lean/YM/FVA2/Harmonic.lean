import YM.FVA2.Hessian
import YangMills.WilsonProof.NativeSupport.YM.Extra.WEAK_SCALING_ACTLAW.Color

/-!
# Cost of actually imposing mean-zero complement on site ghosts

At a source-free or physical tree-equivalent insertion, the global site phase
factor cancels. It would not be correct for BV generator vertices. In this file
we identify the *site tangent determinant* with precisely the projected one in this
case; later uses for MS comparison with sources must check actual marks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Trans
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart
open Function Finset Filter Set Metric MeasureTheory Precision Inherit Push.Loops TreeBasis
open Wilson Based GaussianScore MultiGauge MS.Orbit MS MS.Orbit.Cog MS.Swirl Green MS.Bare -- avoid step names
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable (G : Gauge) (n : Side) (hn : _root_.Even n.val)

local notation "D" => rim n
local notation "C"=> Cone G n
local notation "R"=> plan G n

section turnA
-- prefer Euler sign convention from Manuscript; Ω=(u,u), volts shift is [A,u]
variable {U:Set G.El}{r:ℝ}(H : LocalH.Geom G U (ball 0 r))
include H
lemma radialTurn {v:G.Color}(h:v∈ball 0 r)(u:G.Color): Maurer.voltage v (u,u)= G.ad (-u) v := by
   let F(t:ℝ):= G.adjoint (G.lieExp (t • (-u))) v; have hv : ∀ t:ℝ, F t∈ ball 0 r:= fun t=> by simpa [F] using h
   have he:= Maurer.amp (u,u) H h;
   have ht (t:ℝ) : F t= G.plog (G.mat (Maurer.step (u,u) v t)) := by
       obtain hx:= Maurer.snap_on H (hv t);
       rw [← hx]; unfold Maurer.lie F; rw [Maurer.runby]; unfold Maurer.step; rw [smul_neg, Next.SectorChange.exp_negative, inv_inv]
   rw [← show F = (fun t=> G.plog (G.mat (Maurer.step (u,u) v t))) from funext ht] at he; exact he.unique (Extra.WeakScaling.Color.tangent _ _)
end turnA

-- post gauge constant

def coverG (q : GSite n→G.Color)(u:Cone G n)(i:Edge (Site n)) : G.Color:= Maurer.voltage (coverL G n u i) (siteCopy G n q i.1,siteCopy G n q (i.1+step i.2))
lemma displayed (x:Cone G n)(q:GSite n→G.Color)(i:OEdge n): coverL G n (TreeBasis.turn G (rim n) x q) i.val= coverG G n q x i.val:= by
   rw [coverL_at]; unfold coverG; rw [coverL_at]; rfl

include hn
lemma formal_cover (x:Cone G n) {s : Set G.El}{r:ℝ} (H : LocalH.Geom G s (ball 0 r))(h:∀ i:Edge (Site n), coverL G n x i ∈ ball 0 r) (p:GSite n→ G.Color) (i:Edge (Site n)):
   coverL G n (TreeBasis.turn G (rim n) x p) i= coverG G n p x i:= by
   have he i: coverG G n p x (Orb.reflect i)= -coverG G n p x i:= by
        unfold coverG; simp only [ Orb.reflect ]; -- avoid rw fails? undo
        rw [show coverL G n x (-i.1-step i.2,i.2) = - _ from cover_reflect G n hn x i];
        have hneg (u:Site n) : siteCopy G n p (-u)=siteCopy G n p u:=by simp [siteCopy]
        rw [sub_add_cancel, show -i.1-step i.2= -(i.1+step i.2) by abel, hneg,hneg]
        exact Maurer.comeback_field ((siteCopy G n) p i.1,(siteCopy G n) p (i.1+step i.2)) H (h i)
   by_cases hx:eR i=i
   · exact displayed G n x p (⟨i,hx⟩:OEdge n)
   have hR : eR (Orb.reflect i)=Orb.reflect i:=(eR_reflect _).trans ((eR_spec i).resolve_left hx)
   have hm: coverL G n _ (Orb.reflect i)=coverG G n p x (Orb.reflect i):= displayed G n x p (⟨_,hR⟩:OEdge n)
   rw [he,cover_reflect G n hn] at hm; exact neg_injective hm

lemma stableGlobal (x:Cone G n) {s:Set G.El}{r:ℝ}(H:LocalH.Geom G s (ball 0 r)) (h:∀ i:Edge (Site n), coverL G n x i ∈ ball 0 r)
    (he:Transverse G n x)(u:G.Color): literal G n (TreeBasis.turn G (rim n) x (fun _=>u))=0:= by
    let p b: Cone G n := TreeBasis.turn G (rim n) x (fun _=>b)
    have hx i: coverL G n (p u) i= G.ad (-u) (coverL G n x i) := (formal_cover G n hn x H h (fun _=>u) i).trans (radialTurn G H (h i) u)
    apply mixed_zero G n (p u); intro a; funext i
    rw [Green.divergence_v]; simp_rw [Green.back_of,Colour,GColor,hx];
    -- remove component index. exact equivariance of linear map at color
    let b(k:Axis):= coverL G n x (i-step k,k)-coverL G n x (i,k)
    have hh: ∑ k:Axis,b k=0:= by apply PiLp.ext; intro j; rw [WithLp.ofLp_sum,Finset.sum_apply]; have h:= congr_fun (he j) i; rw [Green.divergence_v] at h; exact h
    trans (∑ k:Axis, G.ad (-u) (b k)) a; · rw [WithLp.ofLp_sum, Finset.sum_apply]; simp only [b,map_sub]; rfl
    rw [← map_sum,hh,map_zero]; rfl

lemma mean_at (p:Param G n) (b:Wilson.Field G n) {s:Set G.El}{r:ℝ}(H:LocalH.Geom G s (ball 0 r)) (h:∀ i, coverL G n ((plan G n).L b) i∈ ball 0 r) :
   (plan G n).ghosts b p= literal G n (TreeBasis.turn G (rim n) ((plan G n).L b) (meanZero G n p)):= by
   have hv (q: Param G n) : meanZero G n q=guarded G (rim n) q - fun _=>averageG G n (guarded G (rim n) q) := rfl
   unfold SectionBasis.ghosts; rw [LinearMap.comp_apply,planned,hv,map_sub,map_sub,stableGlobal G n hn _ H h (gauges G n hn b),sub_zero]; rfl
end YM.FVA2.Trans
