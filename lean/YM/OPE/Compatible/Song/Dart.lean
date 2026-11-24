import YM.OPE.Compatible.Song.Sub
/-!
# Reconstruction pans. Climbing in degree and height. Keep exact geometry.
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
variable {I W:Type} {N:I→ Side}{φ:Filter I}{Z:I→ℝ}{p q z:Forge G N}
variable {M:I→ℕ}(A:Audience φ Z N M r) (s:Phase)
local notation "B"=>fun i:I=>bark (M i)
local notation "E°"=> fun i:I=>leash r (M i)
--- zero stage shift
include A
lemma levelH (hp: EarthX (B) φ Z p d)(h:gapV p s.val φ) (hr:Filμ (B) φ Z (eyeR p s) 0): ∃ E:Forge G N, EarthX (fun i=>leash r (M i)) φ Z E d ∧ EarthX (B) φ Z (p-E) d∧gapV (p-E) (s.val+1) φ:=by
       let f:= eyeR p s; have he:∀ᶠ i in φ,f i=(Claw.rank (f i) 0):=by
            refine hr.tariff.mono fun i hi=>?_ ; exact (Tall.allot hi).trans (Finset.sum_range_one ..) -- f unfolds
       have hF:∀ᶠ i in φ,Crisp ((E°) i) (f i):= he.mono fun i hi=>by constructor; intro x y _; calc
            f i x=jet (f i) 0 x:=congr_fun hi _
            _=jet (f i) 0 y:= (jet_zero ..).trans (jet_zero ..).symm
            _= _:= (congr_fun hi y).symm
       obtain ⟨z,hz,hZ,hh⟩:= PorchE A f (Filμ.mk hF hr.tariff hr.loud) (he.and (hushed _ h hp.mass)); let Y:= LiftA s z; have ht: EarthX (E°) φ Z Y d:= (EarthX.mk hz hZ).below A.fair s (Nat.zero_le _); have hu:EarthX (B) φ Z Y d:= ht.further (fun _=>cure ..)
       refine ⟨Y,ht,hp.shift A.fair hu,lapse (h.sub (Pulse z s)) (hh.mono fun i hi=>?_ )⟩; unfold Y; rw [eye_sub, Pi.sub_apply,fling,hi]; exact sub_self (f i)
omit A in lemma embryo {h:Finset W}{f:W→Forge G N} (s:Phase) (hp:∀ i∈h, gapV (f i) s.val φ): gapV (∑ i∈h,f i) s.val φ:=by
       induction h using Finset.induction_on with
       | empty=> rw [sum_empty];intro i hi; refine Eventually.of_forall fun j=> ?_ ; fin_cases i<;> rfl
       | insert i z hi ih=> rw[sum_insert hi]; exact (hp _ (mem_insert_self ..)).sum (ih (fun j hj=> hp j (mem_insert_of_mem hj)))
lemma PeakR (X:Finset W) (p:W→Forge G N)(h:∀ i∈X,EarthX (B) φ Z (p i) (k+1)) (hv:k+1 ≤ d+s.val): let V:=∑ i∈X,LiftA s (p i); EarthX (B) φ Z V d∧ gapV V s.val φ ∧ Filμ (B) φ Z (eyeR V s) (k+1):=by
       intro V; refine ⟨EarthX.march A.fair X (fun i=>LiftA s (p i)) (fun i hi=> (h i hi).below A.fair s hv), embryo s (fun i h'=> Pulse (p i) _),?_⟩; unfold V; rw [eye_sum]; apply Filμ.totals A.fair; intro i hi; rw [fling]; exact (h i hi).pay.roll 0
end YM.OPE.Merchant
