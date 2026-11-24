import YM.OPE.Compatible.Glim.Psy
/-! # covariance.EOM form -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell
variable {I J E:Type}[Fintype I](p:I)(b:Bool)(S:Score I J)
local notation "B"=> Phone G
open Score
local notation "μ"=> Tested.germ
variable {Y:Keys G I→ G.Color}{f g:Keys G I→ℝ}{r:ℕ}
structure insured (f:Keys G I→ℝ):Prop where
     march : ∀ x y (s:Tile G J), S.dress s (put x)=put y→f x=f y
structure rooted (Y:Keys G I→ G.Color):Prop where
     march : ∀ x y (s:Tile G J), S.dress s (put x)=put y→Y y=G.adjoint (s (S.start (p,b))) (Y x)
variable {p b S} {x y: Keys G I}
lemma gong (hf:insured S f)(hq:insured S g)(hs:rooted p b S Y) (u:Tile G J)(V:ℝ)(H:Pier b (x p))(ht:Pier b (y p))(hx:S.dress u (put x)=put y) (h₀:ContDiffAt ℝ ω Y x)(h₁:ContDiffAt ℝ ω Y y)(h₂:ContDiffAt ℝ ω f x)(h₃:ContDiffAt ℝ ω f y)(h₄:ContDiffAt ℝ ω g x)(h₅:ContDiffAt ℝ ω g y):
    τPower p b f g Y r V x=τPower p b f g Y r V y:=by
       let t:=u (S.start (p,b)); let A:= (G.adjoint t).toContinuousLinearMap; have he:DColor b p Y y ∘L A= A∘L DColor b p Y x:= brake H ht u hx Y h₀ h₁ A (fun x y h=> hs.march x y u h)
       have hv(k:Keys G I→ℝ)(v:G.Color)(h:insured S k) (hp:ContDiffAt ℝ ω k x)(hq:ContDiffAt ℝ ω k y): DColor b p k y (A v)=DColor b p k x v:=by have h:= brake H ht u hx k hp hq (ContinuousLinearMap.id ℝ ℝ) (fun a b h'=> (h.march a b u h').symm); exact DFunLike.congr_fun h v
       unfold τPower; rw [cappe (t:=t) he]; unfold ψPower; rw [show Y y=A (Y x) from hs.march x y u hx]; simp only[_root_.smul_apply,_root_.add_apply]; rw [hv f _ hf h₂ h₃, hv g _ hq h₄ h₅]
lemma crestV (h:Variance.Cand r Y)(hp:Once f g)(hf:insured S f)(hh: insured S g)(hv:rooted p b S Y): S.Marbles (Cake p b f g Y r):= (Drift.pores S (CakeB p b f g Y r)).mpr (by
     intro x y s hw; let X:=Gael.ratioU x; let A:= Gael.ratioU y; have hX:= Gael.walk x hw.hX hw.gx; have hA:= Gael.walk y hw.hY hw.gy; refine (Mixr (p:=p) (b:=b) h hp X hX).equality ((Mixr (p:=p) (b:=b) h hp A hA).cong ?_); have ht:Tendsto x μ (𝓝 0):= hw.gx ▸ hw.hX.continuousAt.continuousWithinAt; have hz:Tendsto y μ (𝓝 0):=hw.gy ▸ hw.hY.continuousAt.continuousWithinAt
     filter_upwards [hw.law.filter_mono nhdsWithin_le_nhds,Tested.eventually_pos, ((continuous_apply p).continuousAt.tendsto.comp ht).eventually (treat G b), ((continuous_apply p).continuousAt.tendsto.comp hz).eventually (treat G b),ht.eventually (h.smooth.eventually (by simp)),hz.eventually (h.smooth.eventually (by simp)),ht.eventually (hp.sm.eventually (by simp)),hz.eventually (hp.sm.eventually (by simp)),ht.eventually (hp.sg.eventually (by simp)),hz.eventually (hp.sg.eventually (by simp))] with v h₀ (ht:0 < v) hu hV h₁ h₂ h₃ h₄ h₅ h₆; unfold X A Gael.ratioU; rw [smul_inv_smul₀ ht.ne', smul_inv_smul₀ ht.ne']; exact gong hf hh hv (s v) v hu hV h₀ h₁ h₂ h₃ h₄ h₅ h₆)
omit [Fintype I] in lemma hush0 {f:E→ℝ}[NormedAddCommGroup E][NormedSpace ℝ E]: Hush f 0:=fun _ _ h=>False.elim (Nat.not_lt_zero _ h)
-- normalized Heading V doesn't need exact f0.
end YM.OPE.Variance
