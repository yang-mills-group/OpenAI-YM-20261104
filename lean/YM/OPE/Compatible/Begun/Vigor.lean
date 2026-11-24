import YM.OPE.Compatible.Begun.Owe
/-!
# Tensor Schur identity
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d:ℕ}{K:KernelChoices}
section vec
noncomputable abbrev Prog (C:KernelChoices)(v:Train r)(G:Gauge)(n:Side):= tensor G (Precision.K ((pink C.penalty v).acts n))
abbrev PhV (C:KernelChoices)(v:Train r)(G:Gauge)(n: Side):=tensor G (lineC (ShellRow C v) n)
abbrev lat {n:Side}{r:ℕ}(u:form r n)(j:G.ColorIndex): Vec G n r:=fun i=> if i.2.2=j then u (i.1,i.2.1) else 0
lemma componentLat (j i:G.ColorIndex)(u:form r n):component (lat u j) i= if i=j then u else 0:=by ext x; by_cases h:i=j<;>simp [lat,h,component,ix]
lemma mulYZ (A:Matrix (Body j n) (Body i c) ℝ)(q:form i c)(j:G.ColorIndex):tensor G A *ᵥ lat q j=lat (A*ᵥq) j:=by
     funext v; obtain ⟨x,b,u⟩:= v; change component (tensor G A*ᵥlat q j) u (x,b)=component (lat (A*ᵥq) j) u (x,b); rw [component_mul,componentLat,componentLat]; by_cases h:u=j; rw [if_pos h,if_pos h];rw [if_neg h,if_neg h,mulVec_zero]
lemma dotYZ (u:form r n)(j:G.ColorIndex)(v:Vec G n r): dotProduct v (lat u j)=dotProduct (component v j) u:=by
     rw [component_dot]; simp_rw [componentLat]; rw [Finset.sum_eq_single j]; rw [if_pos rfl]; intro i _ hi; rw [if_neg hi, dotProduct_zero]; simp
lemma alignZ (C:KernelChoices)(v:Train r)(G: Gauge)(h:4≤ r): (Prog C v G n)ᵀ=Prog C v G n:=by rw [Prog,tensor_transpose,KY v h (K:=C)]
lemma HealthN (h:4≤r)(v:Train r)(q:Vec G n 1)(hp:Health (Prog K v G n) q) : Prog K v G n *ᵥ (PhV K v G n*ᵥ q)=q :=by
     funext i; obtain ⟨x,b,u⟩:= i; let Q:=Prog K v G n; let P:=PhV K v G n; change component (Q*ᵥ( P*ᵥ q)) u (x,b)=component q u (x,b); unfold Q P Prog PhV; rw [component_mul,component_mul]; refine congr_fun (lineSolve v h _ (K:=K) ?_) _; intro w hw; rw [← dotYZ]; apply hp; rw [Prog,mulYZ, hw]; ext1 x; unfold lat; split<;>rfl
lemma raster (v:Train r)(x:Vec G n 0): Prog K v G n *ᵥ (FreeResolvent.gradient x)=0:=by
     funext i; obtain ⟨x',i,j⟩:=i; change component (Prog K v G n *ᵥ FreeResolvent.gradient x) j (x',i)=0; unfold Prog FreeResolvent.gradient; simp_rw [component_mul,mulVec_mulVec (component x j), K_kills, zero_mulVec]; rfl
lemma amplePG (v:Train r)(h:4≤r): (Prog K v G n).PosSemidef := by
      let A:=Prog K v G n; have he:A.IsHermitian:=by unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact alignZ _ _ _ h
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg he (fun x=>?_); rw [star_trivial,component_dot]; unfold Prog; simp_rw [component_mul]; exact Finset.sum_nonneg fun i _=> by simpa only [star_trivial] using (KF (K:=K) (n:=n) v h).dotProduct_mulVec_nonneg (component x i)
end vec
end YM.OPE.Cascade.Paver
