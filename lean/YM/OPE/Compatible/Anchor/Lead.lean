import YM.OPE.Compatible.Anchor.View
/-! # Reads from Tamp.R.E.Frame. weighted radius, polarization.
   High power bought at root. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Labels
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Work.F08
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver FreeResolvent WithLp
open Drift Char Silt Silt.Float Module Page Planned.PrimaryIntegral295.Carrier
variable {i j d k m r l:ℕ}{Z I J M E F:Type}{n:Side}
local notation "Fω"=> fieldX (Shade G)
local notation "W!"=>Alphabet G d
noncomputable def jetΦ (G:Gauge)(i:ℕ): Taylor G i→ₗ[ℝ] fieldX (Shade G) where
     toFun u:= ledge u.val
     map_add' _ _:=rfl
     map_smul' _ _:=rfl
noncomputable abbrev brushW (k:ℕ)(i:Fin d)(t:ℝ): Alphabet G d→ₗ[ℝ] fieldX (Shade G):=
      t^(i.val+k) • (jetΦ G i.val ∘ₗ LinearMap.proj (φ:=fun j:Fin d=>Taylor G j.val) i)
noncomputable def showerW (d:ℕ)(p:ℝ): Alphabet G d→ₗ[ℝ] fieldX (Shade G):=∑ i,brushW 1 i p
lemma BrushQ (x:Alphabet G d)(t:ℝ): Quiet (showerW d t x) d:=by rw [showerW,LinearMap.sum_apply]; generalize (univ:Finset (Fin d))=s; induction s using Finset.induction_on with
    | empty=> rw [sum_empty]; exact ⟨0,le_rfl,fun i=>by rw [Pi.zero_apply,norm_zero,zero_mul]⟩
    | insert i s hi ih=> rw [sum_insert hi]; apply quietAdd _ ih; let A:= t^(i.val+1); have hp: A • jetΦ G i.val (x i)= jetΦ G i.val (A • x i):=(map_smul ..).symm; change Quiet (A • jetΦ G i.val (x i)) d; rw [hp]; exact quiet_up (low_quiet (ledgeL (A • x i).val)) i.isLt
lemma brushOne (x:Alphabet G d)(i:Fin d)(t:ℝ): showerW d t (monoX i (x i))= jetΦ G i.val (t^(i.val+1) • x i):=by
      rw[showerW,LinearMap.sum_apply, Finset.sum_eq_single i]; rw [map_smul]; change (_:ℝ) • jetΦ _ _ (monoX i _ i)=_; rw [monoX,Pi.single_eq_same]
      · intro j _ h; change (_:ℝ) • jetΦ _ _ (monoX i _ j)=_; rw [monoX,Pi.single_eq_of_ne h,map_zero,smul_zero]
      simp
noncomputable def PondΦ (p:cope G r m) (h:r*d ≤ m)(t:ℝ): Chord G d r where
     toFun x:= wholeX p.val fun i=>showerW d t (x i)
     map_update_add' x i a b:=by
         let u(x:Fin r→Alphabet G d):= fun i=>showerW d t (x i); change _=wholeX _ (u _)+wholeX _ (u _); apply choir i (patent_till p) (fun _=> BrushQ _ t) (fun _=> BrushQ _ t) ?_ ?_ ?_ -- args γ
         · simpa using h
         · rw [update_self,update_self,update_self,_root_.map_add]
         intro j hj; simp [update_of_ne hj]
     map_update_smul' x i a b:=by
         let u(x:Fin r→Alphabet G d):= fun i=>showerW d t (x i); change wholeX _ (u _)=a*_ ; apply choir_scalar i
         · unfold u;rw [update_self,_root_.map_smul]; simp
         intro j hj; unfold u; simp [update_of_ne hj]
-- φ to polar series
lemma shower_one (p:cope G r m)(h:r*d≤m)(t:ℝ)(x: Fin r→ Alphabet G d)(k:Fin r→ Fin d): PondΦ p h t (fun i=> monoX (k i) (x i (k i)))=t^rankX k • solidX p.val k x:=by
       let v(i):= monoX (k i) (x i (k i)); let q:=PondΦ p h t; have hp (s:Fin r→ Alphabet G d)(t:ℝ): PondΦ p h t s=wholeX p.val (fun i=>showerW d t (s i)):=rfl
       rw [hp]; simp_rw [brushOne,_root_.map_smul]; unfold wholeX; unfold solidX wholeX; rw [smul_eq_mul,← tsum_mul_left]; refine tsum_congr fun i=>?_ ; unfold wordX rankX; rw [mul_left_comm]; apply congr_arg; simp only[Pi.smul_apply,smul_eq_mul,prod_mul_distrib,prod_pow_eq_pow_sum];rfl
lemma showerView (p:cope G r m)(h:r*d≤m)(t:ℝ)(x: Fin r→ Alphabet G d): PondΦ p h t x=∑ k:Fin r→Fin d,t^(rankX k) • solidX p.val k x:=by rw[deckSum]; simp_rw[shower_one p h t x]
end YM.OPE.Variance
