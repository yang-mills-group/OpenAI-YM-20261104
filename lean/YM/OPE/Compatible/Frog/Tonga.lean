import YM.OPE.Compatible.Frog.Gall
/-!
# Marker pulse. capacity relations and lowest phase. lift conditioning
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l:ℕ}
variable {τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
lemma oak (p:T!)(h:p∈ solar G d τ) (x:Phase) (hx:∀ i<x,p i=0): p x∈ bed G (d+x.val) (τ x):=by
     intro i; let K:=d+x.val; let f:=spread G d τ p; let q:=f x i; have ht:Volume (f x) K (τ x) ‖p x‖:=sproutV ..; by_cases he:i≤ K; swap
     · rw [show lilies (τ x) _ _ (p x) i=0 from ht.1 i (lt_of_not_ge he)]; exact (cope G i (τ x)).zero_mem
     have hu:Rainbow f:=h.1; have hg: soot (τ x) q ‖p x‖:=ht.2 i; obtain ⟨hh,H⟩:= Grid.walkL (Q:=f) (d:=d) h.2 x (fun i hi=>show (lilies (τ i) _ _ (p i))=0 from by rw [hx i hi,map_zero]) (sootS hg) he (hu x i); exact ⟨⟨_,hg⟩,hh,H,hu x i⟩
-- Suspension of pulses. produce later layers OMIT consumption.
def glide (X:Muse G)(p:Phase):Muse G:= fun j=> if j<p then 0 else X ( ⟨j.val-p.val,(by have h:=j.isLt;omega)⟩)
lemma glide_nil (X:Muse G){i j:Phase}(h:i<j): glide X j i=0:=if_pos h
lemma glide_me (X:Muse G)(p:Phase):glide X p p=X 0:=by simp [glide]
lemma baton (p: Muse G)(i:Phase)(d:ℕ)(x:Bid.Dir G n)(u:Site n): inkM (glide p i) d u x= Ū^i.val * inkM p (d+i.val) u x:=by
     let Q:= spool G n x; have ht(a b:Phase )(h:a≤ b):
          Flair (glide p a b) (d+b.val) Q u= Flair (p ⟨b.val-a.val,(by have hb:=b.isLt;omega)⟩) ((d+a.val)+(b.val-a.val)) Q u:=by
               unfold glide; rw [if_neg (not_lt.mpr h), show d+a.val+(b.val-a.val)=d+b.val from by have hk:a.val≤ b.val:=h; omega]
     apply JetS.eta
     · fin_cases i
       · change Flair _ (d+0) Q u= ((Ū^0)*_).s; erw [pow_zero,one_mul, show (glide _ (0:Phase)) _= _ from glide_me p 0];rfl
       · change Flair _ (d+0) Q u= ((Ū^1)*_).s; erw [show glide _ _ _=0 from glide_nil p (show (0:Phase)<1 by decide),flair0,pow_one]; simp [Ū]
       change Flair _ (d+0) Q u= ((Ū^2)*_).s; erw [show glide _ _ _=0 from glide_nil p (show (0:Phase)<2 by decide),flair0]; simp [Ū,pow_succ]
     · fin_cases i
       · change Flair _ (d+1) Q u= ((Ū^0)*_).l; erw [pow_zero,one_mul,ht 0 1 (by decide)];rfl
       · change Flair _ (d+1) Q u= ((Ū^1)*_).l; erw [pow_one, ht 1 1 (by rfl),JetS.ml_l]; change _=(0:ℝ)* _+1*_; erw [zero_mul,one_mul,zero_add];rfl
       change Flair _ (d+1) Q u=((Ū^2)*_).l; erw [show glide _ _ _=0 from glide_nil p (show (1:Phase)<2 by decide),flair0];simp [Ū,pow_succ]
     fin_cases i
     · change Flair _ (d+2) Q u=((Ū^0)*_).h; erw [pow_zero, one_mul, ht 0 2 (by decide)];rfl
     · change Flair _ (d+2) Q u=((Ū^1)*_).h; erw [pow_one, ht 1 2 (by decide)]; simp only [Ū,JetS.ml_h,zero_mul,one_mul,zero_add,add_zero];rfl
     change Flair _ (d+2) Q u=((Ū^2)*_).h; erw [ht 2 2 (by rfl)]; simp only [Ū,pow_two,JetS.ml_h,JetS.ml_s,JetS.ml_l,zero_mul,one_mul,zero_add, add_zero];rfl
lemma glider (X:Muse G)(p:Phase)(h:Pathic (d+p.val) X): Pathic d (glide X p):=by
     intro n x;rw [show inkM _ _ x=(fun _=>Ū^p.val)*inkM X (d+p.val) x from funext fun r=> baton X p d r x]; exact prodMar _ (staysP (tor n) _) (h n x)
structure Aware (d:ℕ)(τ:Phase→ℕ):Prop where
     credit (i:Phase):2*(d+4) +45 ≤ τ i
     margin (i j:Phase)(h:i<j): τ j+2*(d+4)+1 ≤ τ i
lemma Aware.mono (h:Aware d τ): Antitone τ:=fun i j hx=>by by_cases he:i=j; subst j;rfl; exact le_trans (Nat.le_add_right .. |>.trans (Nat.le_succ _)) (h.margin _ _ (lt_of_le_of_ne hx he)) -- ℕ
end YM.OPE.Drift
