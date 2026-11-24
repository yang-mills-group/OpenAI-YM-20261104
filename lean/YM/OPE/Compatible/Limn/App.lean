import YM.OPE.Compatible.Limn.Rote
/-! # Interior basis spherical costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Limn
open Function Filter Set MeasureTheory Lattice Laurent RG Matrix Precision Exterior Tree Push Push.AbsoluteSums Wilson Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Type}
open Next.SectorChange Next.SectorChange.Schur PertExtension Series Libra GaussianScore Flume Flume.Page Flume.Script Flume.Virgin Zeph
open AnalyticNext.QuarticMatch Radius Estimate Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom AnalyticNext.QuarticMatch.Local
open Cascade Rill Votive Stationary Progress.StationaryScenes Work.F03 Next.Free Work.F05 Glass Coin Pilot Next.Foundations Work.F08 FreeResolvent
open PhysicalNext.Repeat.Aroma
variable {t r R B b ε:ℝ}{m:ℕ}
variable {S:StepData c f}{F:Forest S.ratio} {I:Seats F}
open Green (wt)
open Finset Module
abbrev Rubric (G:Gauge)(I:Seats F):= (↥I) × G.ColorIndex
noncomputable def shout (G:Gauge)(I:Seats F): Rubric G I ↪ Key F G := Function.Embedding.prodMap (Embedding.subtype (·∈ I)) (Embedding.refl _)
noncomputable def Tip (G:Gauge)(X':Type)[Fintype X']: Basis (X' × G.ColorIndex) ℝ (Keys G X'):= Basis.reindex (Pi.basis fun _ : X' => (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis) (Equiv.sigmaEquivProd _ _)
lemma tipS (u:Rubric G I): stake I (Tip G (↥I) u)= countingBasis F G (shout G I u):=by
       rw [Tip, Basis.reindex_apply,Pi.basis_apply,countingBasis_apply]; funext i; by_cases h:i∈ I
       · rw [show stake I _ i=_ from stake_on I ⟨i,h⟩ _]; change Pi.single (M:=fun _=>G.Color) u.1 (EuclideanSpace.basisFun G.ColorIndex ℝ u.2) (⟨i,h⟩:↥I)=Pi.single (M:=fun _=>G.Color) u.1.val _ i; by_cases hv:i=u.1.val
         · subst i; simp; rfl -- q
         rw [Pi.single_eq_of_ne (show (⟨i,h⟩:↥I) ≠ u.1 from fun hp=>hv (congr_arg Subtype.val hp)),Pi.single_eq_of_ne hv]
       rw [stake_off I _ i h]; exact (Pi.single_eq_of_ne (M:=fun _=>G.Color) (fun hp: i=(shout G I u).1=>h (hp.symm ▸ u.1.property)) _).symm
lemma Tip_ψ [Fintype X] [DecidableEq X] (u:X × G.ColorIndex) (p:Keys G X):cash (Tip G X) p u=p u.1 u.2:=by
       -- basis fun
       let A:= Tip G X; change (A.repr p) u=_; unfold A Tip; simp [Pi.basis_repr]
lemma chant_sum (X) [Fintype X](p:Keys G X): ∑ i:X, ‖p i‖^2=sumSq (cash (Tip G X) p):=by classical unfold sumSq; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; simp_rw [Tip_ψ]; exact (by simp_rw [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]) -- lemma name
variable (I)
lemma chunk (p:Keys G (↥I)) : cash (countingBasis F G) (stake I p)=Ext (shout G I) (cash (Tip G (↥I)) p):=by
       let z:=shout G I; funext i; change cash (Tip G F.Free) (stake I p) i=_; rw [Tip_ψ]; by_cases he:i.1∈I
       · let t:Rubric G I:=(⟨_,he⟩,i.2); rw [show Ext z (cash (Tip G (↥I)) p) i= cash _ _ _ from covers z _ t, Tip_ψ]; rw [show stake I p i.1=_ from stake_on I ⟨_,he⟩ p]
       rw [stake_off I p i.1 he] -- color coe? Pi norm
       exact (coversOut z (cash (Tip G (↥I)) p) i (fun h=>by obtain ⟨a,ha⟩:=h; exact he (ha ▸ a.1.property))).symm
end YM.OPE.Limn
