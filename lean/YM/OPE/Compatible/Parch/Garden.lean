import YM.OPE.Compatible.Parch.Flint
/-!
# Tensor relations. Beacons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {i j r d m k l:ℕ}
section
variable {X E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [NormedAddCommGroup X][NormedSpace ℝ X]
lemma shine (P Q:X→L[ℝ] E) (f:E→F)(hf:ContDiffAt ℝ ω f 0)(h:∀ v,f (P v)=f (Q v))(j:ℕ): ∀ x: Fin j→X, Tensor.coeff f j 0 (P∘x)=Tensor.coeff f j 0 (Q∘x) := by
      let p:=Tensor.coeff f j 0; let A:= p.compContinuousLinearMap (fun _=>P); let B:=p.compContinuousLinearMap (fun _=>Q); have he: Tensor.Sym p:= Tensor.coeff_symm (hf.of_le le_top)
      have hz(x:X): Tensor.diagonal A x= Tensor.diagonal B x:=by
            change rank f j (P x)= rank f j (Q x); unfold rank; rw[←WardBin.leading_tensor (P x) f (hf.of_le le_top),← WardBin.leading_tensor (Q x) f (hf.of_le le_top)]; apply congr_arg; funext v; rw [←map_smul,←map_smul,h]
      let hx:= Tensor.ext_diag A B (fun v s=>he (fun i=>P (v i)) s) (fun v s=> he (fun i=>Q (v i)) s) (funext hz); exact fun v=> DFunLike.congr_fun hx v
variable {g:E→F}
-- relation under CL comparisons, arbitrary index families
lemma crossD {D:E→L[ℝ] X} (p: E→F)(hp:ContDiffAt ℝ ω p 0)(ht:∀ x y,D x=D y→p x=p y): ∀ x y: Fin j→E,(∀ i,D (x i)=D (y i))→Tensor.coeff p j 0 x= Tensor.coeff p j 0 y:=by
       let f:E×E→L[ℝ] E:= ContinuousLinearMap.fst ℝ E E; let g:E×E→L[ℝ] E:= ContinuousLinearMap.snd ℝ E E; let P:=(D ∘L f-D ∘L g).ker; let X:= P.subtypeL; let U:=f∘L X; let V:=g∘L X; have hv(x:P):D (U x)=D (V x):=sub_eq_zero.mp (show D (U x)-D (V x)=0 from x.property)
       intro x y h; let z(i):P:= ⟨(x i,y i),sub_eq_zero.mpr (show D (x i)=D (y i) from h i)⟩; let H:=shine U V _ hp (fun v=>ht _ _ (hv _)) j z; exact H
lemma slideT (p:E→F)(hp:ContDiffAt ℝ ω p 0)(M:X→L[ℝ] E)(h:∀ x y,p (x+M y)=p x)(v:Fin j→E)(w:Fin j→X):Tensor.coeff p j 0 (fun i=>v i+M (w i))=Tensor.coeff p j 0 v:=by
       let f:E×X→L[ℝ] E:=ContinuousLinearMap.fst ℝ E X; let g:E×X→L[ℝ] X:= ContinuousLinearMap.snd ℝ E X; let Q:=f+M ∘L g; exact shine Q f p hp (fun i=>h i.1 i.2) j (fun i=>(v i,w i)) -- αx
end
variable {G:Gauge}{D V:Type}
open Function Filter Set Lattice Laurent Wilson RG Matrix Precision Cascade
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance Merchant Stand
attribute [local instance] Gauge.frobInner
local notation "E!"=>Libra.Keys G D
variable (R:Cascade.Score D V)[Fintype D]
variable {p: E!→ℝ}
lemma shiftY (R:Cascade.Score D V) {p: Libra.Keys G D→ ℝ} (h:LevelA R p)(ht:ContDiffAt ℝ ω p 0)(x:Fin j→ E!)(s: Fin j → V→ G.Color): Tensor.coeff p j 0 (fun i=>x i+gillS R (s i))=Tensor.coeff p j 0 x:=by
       -- finite span pi restrict. CL injection parameter. no require Finite V.
       let g: (Fin j→ℝ)→ₗ[ℝ] V→G.Color := ∑ i:Fin j,(LinearMap.proj i).smulRight (s i)
       let v(i:Fin j):Fin j→ℝ:=Pi.single i 1; have hz(i):g (v i)=s i:=by unfold g v; rw[LinearMap.sum_apply]; simp [Pi.single_apply]
       let M:= LinearMap.toContinuousLinearMap ((gillS R).comp g); have hV(i): M (v i)=gillS R (s i):=by change gillS R _=_; congr 1; exact hz i
       simp_rw [← hV]; apply slideT p ht M (fun x y=> h.tilts x (g y))
lemma entY (p:E!→ℝ)(ht:∀ x:E!,∀ g:G.El,p (glint D g x)=p x)(he:ContDiffAt ℝ ω p 0)(x:Fin j→E!)(g:G.El): Tensor.coeff p j 0 ((glint D g)∘x)=Tensor.coeff p j 0 x:=by
        let z:E!→L[ℝ] E! := (glint D g).toContinuousLinearEquiv.toContinuousLinearMap; exact shine z (ContinuousLinearMap.id ℝ _) _ he (fun y=>ht y g) j x
end YM.OPE.Claw
