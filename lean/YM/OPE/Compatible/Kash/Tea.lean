import YM.OPE.Compatible.Kash.Qib
import YM.OPE.Compatible.Kash.Trill
import YM.OPE.Compatible.Kash.Lease
import YM.OPE.Compatible.Kash.Sump
import YM.OPE.Compatible.Glim.Xpand
/-! # Uniform supplies of finite-angular scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d k m r l:ℕ}{Z I J:Type}
variable {n:Side}{x t:ℝ}
local notation "C!"=> Curtain (Shade G)
local notation "Φ" n:arg=>Bid.Dir G n
section Lift
variable {W I₁:Type}{c n:Side}
local notation "ν"=> Site
variable {p:Script (Shade G) r}
variable (hc:c.val∣n.val)
include hc
lemma Food (p:Script (Shade G) r)(x:Site n)(q:Bid.Dir G c): Flume.Script.value x p (spool G n (Booklet hc G q))=Flume.Script.value (trimT n c hc x) p (spool G c q):=by
        unfold Flume.Script.value scribe; refine tsum_congr (fun b=>congr_arg (p b*·) ?_); apply Finset.prod_congr rfl; intro j _; let Ψ:=trimT n c hc; change spool G c q (Ψ (x+wrap n (b j).1),(b j).2) = _; rw [map_add,lease] -- name
lemma ColumnEq (P:Curtain (Shade G))(k:ℕ)(u:Site n)(Q:Bid.Dir G c): column G P k n u (Booklet hc G Q)=column G P k c (trimT n c hc u) Q:= by unfold column Flair; exact sum_congr rfl fun _ _=>Food ..
omit hc
lemma ColumnUp {P Q:Curtain (Shade G)}{k:ℕ}(h:∀ᶠ n:Side in atTop,column G P k n=column G Q k n):column G P k=column G Q k:=by
       funext n i z; obtain ⟨t,hp⟩:= eventually_atTop.mp h; let u:= n*t; have he:n.val∣u.val:= dvd_mul_right ..; let v:=wrap u (lift i); have hx:trimT u n he v=i:= (lease ..).trans (wrap_lift _); have hv(Q:Curtain (Shade G)): column G Q k u v (Booklet he G z)=column G Q k n i z:=Eq.trans (ColumnEq ..) (hx ▸ rfl) -- subst error
       rw[←hv,←hv,hp u (by exact Nat.le_mul_of_pos_left _ n.pos)]
end Lift
variable {Γ:Z→ℝ}{g:Filter Z} {A:Z→ foliage G}{τ:Phase→ℕ}{P:Z→ solar G k τ}
lemma Usher.bequeath (ht:Tendsto Γ g atTop)(h:∀ m,Usher Γ g A k m)(hv:∀ᶠ i in g,Holds (P i) (A i)): Ibis.Alive g Γ P:=by
        intro m; choose f hf H using fun j:Phase=> (h m j).pays; refine ⟨fun i=> ∑ j,f j i,RateLE.sum ht (fun j _=>hf j),?_ ⟩; filter_upwards [eventually_all.mpr H,hv] with i hH hi j; obtain ⟨t,hT,hW⟩:= (hH j).holds; let F(j:Phase):=Ibis.Goan (P i) j; let a:=Paver.bow t; have ha:=beagle t hT
        have hx:column G a (k+j.val)=column G (F j) (k+j.val):=by
              apply ColumnUp; filter_upwards [hi,hW] with i hy hh; funext v x; rw [show column G (F j) _ _ v x=(mind (P _).val i v x).seq j.val from (vein_i ..).symm,hy,show (A _ i v x).seq j.val= column G t _ _ v x from (congr_fun (congr_fun hh v) x).symm]; exact sum_congr rfl (fun l _=> scoring _ (sootS (hT.2 _)) _ _)
        have he(q : Curtain (Shade G)){c:ℝ}(h:Volume q (k+j.val) m c): Volume q (k+j.val) 0 c:= ⟨h.1,fun i=> soot_le_k _ _ (h.2 i) (Nat.zero_le _)⟩
        have hz : a= F j:=scoreF _ _ (he _ ha) (resin (P i).val (m:=0) (fun _=>Nat.zero_le _) j) (fun _=> stir _) ((P i).property.1 j) (fun v u=> by obtain ⟨y,rfl⟩:=(spool G v).surjective u; exact congr_fun (congr_fun (congr_fun hx v) _) y )
        refine Volume.raise _ (show Volume (F j) (k+j.val) m (f j i) from hz ▸ ha) le_rfl ?_; exact Finset.single_le_sum (fun j _=> (hH j).credits) (mem_univ _)
section
variable {K:Sponsor G}{T:Seasons K}{V:Z→ℝ}(A:(j:Z)→Alps K T i (V j))
variable {I:Z→Type}[∀ i,Fintype (I i)] (p:(i:Z)→I i→RootEdge)(P:(i:Z)→ Libra.Keys G (I i) → G.Color)
variable (ht:Tendsto Γ g atTop)(hK:Arid Γ g p)(e:RootEdge)(b:Bool)(hx:∀ i, BudY e b k (p i) (P i))
variable (h:∀ j:G.ColorIndex,∀ i:Phase,Tonic Γ g (fun i=>(Phone G).coord j ∘ P i) (k+i.val)) (hΓ:RateLE g Γ V 0)
include hx h ht hK hΓ
variable {τ:Phase→ℕ}
lemma Comet {q:Clip}(he:∀ j:Z,(A j).clip=q)(hv:0 ≤ V)(hp:k+1 ≤ d)(hs:G.Simple): ∃ x:Z→ solar G d τ,Ibis.Alive g Γ x ∧∀ i,Holds (x i) (School e b A i (p i) (P i) k):=by
        have ht' :∀ i:Z,∃ x:solar G d τ,Holds x (School e b A i (p i) (P i) k):=by
             intro i; obtain ⟨v,hv,X⟩:= globuleY e b A (p i) (P i) (hx i) hp he hv hs (τ:=τ); obtain ⟨x,-,H⟩:=X i; exact ⟨x,H⟩
        choose x hz using ht'; refine ⟨x, Usher.bequeath ht (fun m=> Usher.grown (DawnY p ht hK e b A P hx h hΓ he hv (m:=m)) hp) (Eventually.of_forall hz),hz⟩
end
end YM.OPE.Variance
