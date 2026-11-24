import YM.OPE.Compatible.Song.Venue
/-! # Turn singular into authorized launches -/
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
variable {I W:Type} {B:I→ Finset (Edge Cover)}{N:I→ Side}{φ:Filter I}{Z:I→ℝ}
variable {K:Sponsor G}{T:Seasons K}{τ:Phase→ℕ}
variable {M:I→ℕ}(A:Audience φ Z N M r)
variable {v:I→ℝ}(V:(j:I)→ Alps K T i (v j)) (P T₀: GlyphQ G N) {P₁: ChartRatio G}
lemma ego_c (N:I→ Side)(X Y:I→solar G d τ): ego G N (X+Y)=ego G N X+ego G N Y:=by
        funext i x; let t:= X i; let s:= Y i; change inkM (spread G _ _ (t+s).val) d 0 x=inkM (spread G _ _ (t).val) d 0 x+inkM (spread G _ _ s.val) d 0 x; change inkM (spread G _ _ (t.val+s.val)) d _ _= _; rw[map_add]; exact Ink_sum _ _ _ _ d _ _ (resin t.val (m:=0) (fun _=>Nat.zero_le _)) (resin s.val (fun _=>Nat.zero_le _))
lemma ego_nil (N:I→ Side): ego G N (0:I→solar G d τ)=0:=by apply add_left_cancel (a:=ego G N (0:I→solar G d τ)); rw [← ego_c,zero_add,add_zero]
namespace Crier
variable {A V P T₀}{hp:4 ≤ i}{hr:LocalRatio P₁}{hs:G.Simple}{hV:0 ≤ v}{R:Patch}{a:Axis}{Y X:I→solar G d τ}{x y:Forge G N}
lemma leanB (h:Crier A V P T₀ hp hr hs hV R a l X x)(hv:Crier A V P T₀ hp hr hs hV R a l Y y): Crier A V P T₀ hp hr hs hV R a l (X+Y) (x+y):=by
       refine ⟨?_,h.prepaid.life.plus_S hv.prepaid.life A.fair,?_⟩; · rw [ego_c]; exact WageK.add h.phased hv.phased
       intro i; exact Submodule.add_mem _ (h.prepaid.spirit _) (hv.prepaid.spirit _)
lemma zeroP : Crier A V P T₀ hp hr hs hV R a l (0:I→solar G d τ) 0:=by
       refine ⟨?_,?_ ,fun _=> Submodule.zero_mem _⟩; · rw [ego_nil]; exact WageK.empty
       intro k; refine ⟨fun _=>0,RateLE.const _ A.fair, Eventually.of_forall fun i j=>?_ ⟩; unfold Goan; rw [show ((0:I→solar G d τ) i).val=0 from rfl,map_zero]; exact ⟨fun _ _=>rfl,fun _=>Sack.zero le_rfl _⟩ -- names
lemma totals (X:Finset W) (u:W→I→solar G d τ)(x:W→Forge G N)(h:∀ i∈X,Crier A V P T₀ hp hr hs hV R a l (u i) (x i)):Crier A V P T₀ hp hr hs hV R a l (∑ i∈X,u i) (∑ i∈X,x i):=by
       induction X using Finset.induction_on with
       | empty=>rw[sum_empty,sum_empty]; exact zeroP
       | insert i s hi ih=> rw [sum_insert hi,sum_insert hi]; exact leanB (h _ (mem_insert_self ..)) (ih (fun i hi=>h _ (mem_insert_of_mem hi)))
end Crier
end YM.OPE.Merchant
