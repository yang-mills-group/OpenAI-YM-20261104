import YM.OPE.Compatible.Glim.Ray
/-! # tail pay. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float
variable {u d s r l k m:ℕ}{W I:Type}{τ:Phase→ℕ}
variable (n:W→Side)(H: ∀ i,Even (n i).val)(T:∀ i,Plot (H i))(p: (i:W)→ Stand.Free (T i))(x: (i:W)→Site (n i))(h:Aware d τ)
local notation "E!" i:arg=>Libra.Keys G (Stand.Free (T i))
variable (S:W→solar G d τ){B:Sponsor G}{Z:Seasons B}{t:ℝ}
lemma SoulsPaid (Y :I→W→Token)(Γ:W→ℝ)(C :  Finset I)(hv:∀ i∈C,Permit n k Γ (Y i)):
     Permit n k Γ (∑ i∈C,Y i):=by induction C using Finset.induction_on with
       | empty=> rw [Finset.sum_empty]; intro i; fin_cases i<;>exact ⟨0,le_rfl,fun i=>by change ‖(0:ℝ)‖≤0 * _ *_; simp⟩
       | insert i C hi ih=> rw [Finset.sum_insert hi]; exact Permit.add n (hv _ (mem_insert_self ..)) (ih (fun i hi=>hv _ (mem_insert_of_mem hi)))
abbrev WTax (e k:ℕ):= (4+(0+8)+4*((e+(2+(k+2)))+6)+(4+8+4*6+(4+8+4*6)))
lemma PortPay (A:Alps B Z s t)(U:∀ i,Bor (H i) A 0) (a:W→Bool) (F:(i:W)→Bid.Dir G (n i)→G.Color)(q:W→Kv)
    (hp:∀ i,Variance.Cand r (F i))(hf:∀ i,AwayZ (H i) (T i) (p i) (q i) (F i))
    (he:∀ j:G.ColorIndex,WindT n 0 (u+2) 1 fun i=>Pawn.mold (WindV (H i) (T i) (F i) j) r) (C : ℝ)(hv:∀ i,m ≤ τ i)(hc:0≤ C)(hz: ∀ i,BeamNear (H i) (T i) (p i) (x i) C)(h:G.Simple)(hr:LocalRatio P)(ht:4 ≤ s)(hU:0 ≤ t):
    let e(i):= Plate (H i) (T i) (p i) (q i);
    let v(i):= Cake (whiz (e i)) ((a i).xor (dir (H i) (e i))) (Dune A) (Rh A) (F i) r
    Permit n (WTax (u+2) d) (PortS n S m) fun i=> ((U i).L (T i)).pay P ((v i ∘ offZ (H i) (T i))* Nyx (H i) (T i) (x i) (S i).val):=by
        intro e v; let O(i:W):= Nyx (H i) (T i) (x i) (S i).val; let V(k:G.ColorIndex)(i:W):=Topper (p i) ((Phone G) k) (a i) (O i); let D(k:G.ColorIndex)(i:W):=Pawn.mold (WindV (H i) (T i) (F i) k) r; let g(k:G.ColorIndex)(i:W):= ((U i).L (T i)).pay P (D k i * V k i); have hh:0 ≤ PortS n S m:=by intro i; change 0 ≤ (_:ℝ)⁻¹^_*_; positivity
        have hj(k:G.ColorIndex):WindT n (0+0) (u+2+(2+(d+2))) (PortS n S m) fun i=> D k i * V k i:=by rw [← one_mul (PortS n S m)]; exact (he k).prod (AiryPaid n H T p x S k a hv C hc hz) zero_le_one
        have hu:Foam (fun _:W=>A):=⟨⟨A.clip,fun _=>rfl⟩,⟨_,hU,fun _=>le_refl _⟩,fun _=>hU⟩; have hx(k:G.ColorIndex): Permit n (WTax (u+2) d) (PortS n S m) (g k):=by
            let Y(i:W):= ((U i).L (T i)).hat P; let Q₀(i:W):=penon ((U i).L (T i)); rw [show g k=fun i=>fair (Chart.tangent G _) (Q₀ i) (Y i) (D k i*V k i) from funext fun i=> ((U i).L (T i)).cutOut hr (Q₀ i) _ (penon_shape _)]; exact channelP (fun _=>A) n H T U (hj k) hh (fun i _=> Lid.hat_full _ hr _) (hTHat n H T _ U h hr rfl hu) ht h
        rw [show (fun i=>_)=∑ k,g k from ?_]; rotate_left; · funext i; erw[Finset.sum_apply]; exact Reflector (H i) (T i) (p i) (a i) A (U i) h hr (q i) r (F i) (hf i) (hp i) (O i) ((T i).composeWard (CloudH _ (S i) _));
        exact SoulsPaid n g (PortS n S m) _ fun i _=> hx i
end YM.OPE.Variance
