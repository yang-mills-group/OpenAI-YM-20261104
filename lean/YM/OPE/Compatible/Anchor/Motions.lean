import YM.OPE.Compatible.Anchor.Pipes
/-! # dimension supply, force Ward on every rank Φ₀. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08 Maxwell
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r n l:ℕ}{Z I J M E F:Type}
local notation "θ"=> 𝓝[>] (0:ℝ)
variable {K:Sponsor G}{S:Seasons K}{u:M→ℝ}{τ:Phase→ℕ}
variable (L:M→Submodule ℝ (solar G d τ))(A:(j:M)→Alps K S i (u j)) {α:Fin (r+1)→Fin k} (X:partX G (r+1) n k)
lemma movingS (s:Finset (Fin (r+1)))(hp:(r+1)*k ≤ τ 0)(he:r+1≤ d)(hG:G.Simple)(h:Forum A L)(hz:n=rankX α)(hx:wiped X.val):
   Obtains (ZTheta u) L (r+1) n (fun x:Alphabet G k=> X.val (fun j=>Oval j s α (x (α j)))):=by
      induction s using Finset.induction_on with
      | empty=> rw[show (fun x:Alphabet G k=> _)=(0:Alphabet G k→ℝ) from funext (fun i=>EndBox X α i hx)]; exact Obtains.zen L
      | insert i s hi ih=>
        let f(x:Alphabet G k) := (fun j=>Oval j s α (x (α j)))
        have ht:= moving L A X s i hp he hG h hz; let a:=α i; let T(x:Alphabet G k):=monoX a (armK G a.val (x a)); let v(x:Alphabet G k):=X.val (f x); let w(x:Alphabet G k):=X.val (update (f x) i (T x)); rw [show (fun x:Alphabet G k=> _) = v+w from ?_]; exact Obtains.plus L ih (show Obtains _ _ _ _ w from ht) hp
        funext x; rw [show (fun j=>Oval j (insert i s) α (x (α j)))=update (f x) i (f x i+ T x) from ?_, MultilinearMap.map_update_add,update_eq_self];rfl -- def
        funext j; by_cases h:j=i
        · subst j; rw [update_self]; unfold f Oval; simp only [LinearMap.comp_apply,if_pos (mem_insert_self ..),if_neg hi]; let Y:= x a; change pat a Y= pat a (Y-armK G a.val Y)+ pat a (armK _ _ Y); rw [← map_add, sub_add_cancel]
        rw [update_of_ne h]; unfold f Oval; simp[h]
lemma BrightStock {r:ℕ}(P: partX G r n k)(hp:r*k ≤ τ 0)(he:r≤ d)(hG:G.Simple)(h:Forum A L)(hx:wiped P.val):
   Obtains (ZTheta u) L r n (fun x:Alphabet G k=> P.val (fun _=>x)):=by
      cases r; next =>
         rw[show (fun x:Alphabet G k=> _)=(0:Alphabet G k→ℝ) from funext (fun x=> (congr_arg P.val (show (fun _ : Fin 0=>x)=(fun _=> glare G k x) from Subsingleton.elim .. )).trans (hx (fun _=>x))) ]; exact Obtains.zen L
      next r=>
        let Y(i:Fin (r+1)→ Fin k)(x:Alphabet G k):= P.val fun j=>monoX (i j) (x (i j)); rw[show (fun x:Alphabet G k=> _) =∑ i,Y i from funext fun i=> (deckSum P.val (fun _=>i)).trans (Finset.sum_apply i _ Y).symm]; apply Obtains.sum L _ _ _ hp; intro i _; by_cases he': rankX i=n
        · rw[show Y i= (fun x:Alphabet G k=> P.val (fun j=>Oval j univ i (x (i j)))) from ?_]; exact movingS L A P univ hp he hG h he'.symm hx; funext x; apply congr_arg P.val; funext j; unfold Oval; simp only [if_pos (Finset.mem_univ j)];rfl
        rw [show Y i=0 from funext fun x=> (show Off G _ _ _ P.val from P.property).Grades i (fun j=> x (i j)) he']; exact Obtains.zen L
end YM.OPE.Variance
