import YM.OPE.Compatible.Anchor.Roots
/-!
# Telescope through offshell occurrences -/
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
noncomputable def stage2 (G:Gauge)(i:ℕ): Taylor G i→ₗ[ℝ] Taylor G i:= LinearMap.id- armK G i
lemma stage_m (x:Taylor G i)(s:G.El):stage2 G i (Taylor.paint s x)= Taylor.paint s (stage2 G i x):=by unfold stage2; rw[LinearMap.sub_apply,LinearMap.sub_apply,map_sub,amuse];rfl
noncomputable def Oval (j:Fin (r+1))(s:Finset (Fin (r+1)))(v:Fin (r+1)→Fin k): Taylor G (v j).val→ₗ[ℝ] Alphabet G k:=pat (v j) ∘ₗ (if j∈s then LinearMap.id else stage2 G (v j).val)
abbrev escalated (Y:Taylor G i):= Y∈LinearMap.range gaugeJet
lemma SFix (g: Fin k)(p:Taylor G g.val)(h:escalated p): glare G k (monoX g p)=monoX g p:=by
     obtain ⟨q,hq⟩:=h; funext i; by_cases he:i=g
     · subst i; subst p; change gaugeJet ((gaugeJet (G:=G) (j:=g.val)).leftInverse ((monoX g (gaugeJet q)) g))= monoX g (gaugeJet q) g; unfold monoX; rw [Pi.single_eq_same,Flume.Script.shines]
     unfold glare; simp [he,monoX]
lemma EndBox (x:Fin (r+1)→Fin k)(w: Alphabet G k)(hx:wiped X.val): X.val (fun j=> Oval (G:=G) j ∅ x (w (x j)))=0:= by
    rw [show (fun j=> Oval _ _ _ _)=fun j=> glare G k (Oval j ∅ x (w (x j))) from ?_]; exact hx _; funext i; unfold Oval; rw [LinearMap.comp_apply, if_neg (Finset.notMem_empty _)]; exact (SFix _ (stage2 _ _ _) (Cog ..)).symm
lemma OvalCov (j:Fin (r+1))(s:Finset (Fin (r+1)))(v:Fin (r+1)→Fin k)(A:Taylor G (v j).val)(u:G.El): Oval j s v (Taylor.paint u A)=spray u (Oval j s v A):=by unfold Oval; rw [LinearMap.comp_apply,LinearMap.comp_apply]; split; exact (spray_one u (v j) A).symm; next h=> rw [stage_m]; exact (spray_one ..).symm
lemma armZero (h:i=0)(x:Taylor G i): armK G i x=0:=by subst i;rfl
-- permute onto 0 via finite swap
lemma moving (s:Finset (Fin (r+1)))(p:Fin (r+1)) (hp:(r+1)*k ≤ τ 0)(he:r+1≤ d)(hG:G.Simple)(h:Forum A L)(hz:n=rankX α):
   Obtains (ZTheta u) L (r+1) n (fun x:Alphabet G k=> X.val (Function.update (fun j=>Oval (G:=G) j s α (x (α j))) p (monoX (α p) (armK G (α p).val (x (α p))))) ) :=by
     let a:= α p; let T:= Equiv.swap 0 p; let q(i:Fin r):=T i.succ; let β:=α∘ q; let v(i:Fin r):Taylor G (Fin.val (β i))→ₗ[ℝ] Alphabet G k:= Oval (q i) s α
     have ht(j:Fin r):q j ≠ p:=fun h=>by apply Fin.succ_ne_zero j; exact T.injective (h.trans (Equiv.swap_apply_left ..).symm)
     let V(x:Alphabet G k) := Function.update (fun j=>Oval j s α (x (α j))) p (monoX a (armK G a.val (x a)))
     by_cases ha:a.val=0
     · rw [show (fun x=>X.val (Function.update (fun j=>Oval j s α (x (α j))) p _))=(0:Alphabet G k→ℝ) from ?_]; exact Obtains.zen L
       funext x; exact X.val.map_coord_zero p (by rw [update_self,armZero ha]; simp [monoX])
     let Z(x:Alphabet G k):= monoX a (armK G a.val (x a)); change Obtains _ _ _ _ (fun x:Alphabet G k=>X.val (V x)); rw [show (fun x:Alphabet G k=>X.val (V x))= fun x: Alphabet G k=> Teas X v (Z x) (fun i=> x (β i)) from ?_]; swap
     · funext x; refine (((show Off G (r+1) n k X.val from X.property).Perms (V x) T).symm).trans (Eq.symm ?_); rw [arrayR]; apply congr_arg X.val; funext j; refine Fin.cases ?_ (fun i=>?_) j; change (monoX a _)= V x (T 0); rw [show T 0=p from Equiv.swap_apply_left ..]; unfold V; rw [update_self]; change Oval _ _ _ _ = V x (q i); unfold V; rw [update_of_ne (ht i)]; rfl
     have hh: a.val=a.val-1+1:=(by omega); apply initial_u L A X v a hh hp he hG h (fun _ _ _=> OvalCov ..) (?_)
     rw [hz,show rankX α=∑ i,(↑(α (T i))+1:ℕ) from (Equiv.sum_comp T _).symm, Fin.sum_univ_succ, show T 0=p from Equiv.swap_apply_left ..]; change a.val+1+rankX β= _; congr 1; omega
end YM.OPE.Variance
