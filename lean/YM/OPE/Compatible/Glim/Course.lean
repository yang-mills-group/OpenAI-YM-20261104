import YM.OPE.Compatible.Glim.Merk
/-! # Local budgets of marker.Serial seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint
variable {n:Side}(H:Even n.val)(T:Plot H)(p:T.Free)(b:Bool){F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]{i k:ℕ}
local notation "L!"=> offZ H T (G:=G)
local notation "E!"=> Keys G T.Free
abbrev Solo (e:edgeV n)(f:Bid.Dir G n→F):Prop:=∀ x y, (∀ i:edgeV n,e≠i → x (whiz i)=y (whiz i)) → f x=f y
abbrev AwayZ (k:Kv)(f:Bid.Dir G n→F):Prop:= ∀ k'≠k,Solo (Plate H T p k') f
lemma SoloT (e:edgeV n)(f:Bid.Dir G n→F)(x:Bid.Dir G n)(h:ContDiffAt ℝ ω f x)(hp:Solo e f): DColor b (whiz e) f x=0:=by
     ext1 v; let A:=lunge (whiz e) b x v; let V(t:ℝ):=x+t • A; have ht:V 0=x:=by simp [V]
     have hz:HasDerivAt V A 0:=by unfold V; simpa using! ((hasDerivAt_id' (0:ℝ)).smul_const A).const_add x
     change fderiv ℝ f x A=0; apply HasDerivAt.unique ((show HasFDerivAt f (fderiv ℝ f x) (V 0) from ht.symm ▸ (h.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hz); rw [show f ∘ V=fun _=> f x from ?_]; exact hasDerivAt_const ..; funext i; apply hp; intro j hj; have he:whiz j ≠ whiz e:=fun h=>hj ((driftB n).injective h.symm); change (V i) (whiz j)=_; unfold V A; simp [lunge, he]
lemma launches (k:Kv)(f:Bid.Dir G n→F)(h:ContDiffAt ℝ ω f 0)(hp:AwayZ H T p k f):
    ∀ᶠ x:E! in 𝓝 0, DColor b p (f∘ L!) x=DColor (b.xor (dir H (Plate H T p k))) (whiz (Plate H T p k)) f (L! x):=by
       let L:= offZ H T (G:=G); filter_upwards [(show Tendsto L (𝓝 0) (𝓝 0) from L.map_zero ▸ L.continuous.tendsto _).eventually (h.eventually (by simp)),dualX H T p b (G:=G)] with x hx ht; ext1 i; let V:= fderiv ℝ f (L x); change fderiv ℝ (f ∘ L) x (lunge p b x i)=_; rw [fderiv_comp x (hx.differentiableAt (by simp)) L.differentiableAt,L.fderiv]; change V (offZ H T (lunge p b x i))=_; rw [ht,map_sum,sum_eq_single k]; rfl; · intro s _ he; exact DFunLike.congr_fun (SoloT _ _ f _ hx (hp s he)) i;
       simp
lemma onceScale {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E→ℝ}{i:ℕ}(h:Hush f i)(hf:ContDiffAt ℝ ω f 0)(v:ℝ): Hush (v • f) i:=by intro x k hk; unfold jet; rw [iteratedFDeriv_const_smul_apply (hf.of_le le_top),_root_.smul_apply]; rw [smul_eq_mul,mul_left_comm,show ((k.factorial:ℝ)⁻¹ * _)=_ from h x k hk,mul_zero]
noncomputable abbrev CostsH(f: Bid.Dir G n→ℝ) :E!→ℝ:= (4:ℝ)⁻¹ • (f ∘ L!)
variable {f g:Bid.Dir G n→ℝ}
abbrev steady_r (v:Bid.Dir G n→ℝ):Prop:=∀ s u,v ∘ shifts s u=v
lemma windH (h:Once f g): Once (CostsH H T f) (CostsH H T g):=by
     let p:= h; have he:=OwnL h (offZ H T); exact ⟨he.sm.const_smul (4:ℝ)⁻¹,onceScale he.zero he.sm _,he.sg.const_smul (4:ℝ)⁻¹⟩
lemma crisp (k:Kv)(Y:Bid.Dir G n→G.Color)(hv: AwayZ H T p k Y)(hp:Variance.Cand i Y)(h:Once f g)(hA:steady_r f)(hQ: steady_r g):
    Cake p b (CostsH H T f) (CostsH H T g) (Y ∘ L!) i= Cake (whiz (Plate H T p k)) (b.xor (dir H (Plate H T p k))) f g Y i ∘ L!:=by
       apply distillEq h hp (windH H T h) (CandL hp L!) L!; filter_upwards [launches H T p b k Y hp.smooth hv,carried H T p b h.sm hA k,carried H T p b h.sg hQ k] with x h hx hp t; unfold τPower ψPower; rw [h]; erw [hx,hp];rfl
end YM.OPE.Variance
