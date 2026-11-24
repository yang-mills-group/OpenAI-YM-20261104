import YM.OPE.Compatible.Begun.Saw
/-!
# Tensor Schur identity. Coordinate polarity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j m:ℕ}{K:KernelChoices}
-- lift tests; kernel annih at ordinary anchors
-- storm pure via pre & resolvent: u= grad y + missing u
lemma origins (x:form 1 n)(he: d 1 n *ᵥ x=0):∃ p:form 0 n, x= Resolvent.missing n*ᵥ x+d 0 n *ᵥ p:= by
     have h:= congr_arg (fun a:Matrix _ _ ℝ=> a*ᵥ x) (Resolvent.reverse n); rw [← mulVec_mulVec,Resolvent.hessian,add_mulVec,← Matrix.mulVec_mulVec] at h
     have hz: curl n *ᵥ x=0:=he; rw [hz,mulVec_zero,zero_add,mulVec_mulVec x,Streamer.gas_comm,←mulVec_mulVec,←mulVec_mulVec, sub_mulVec,one_mulVec] at h; let w:=(grad n)ᵀ*ᵥ (Resolvent.pre n *ᵥx); exact ⟨w,by change x = _+grad n*ᵥ w; rw [show grad n*ᵥ w=_ from h]; abel⟩
-- construct QUIET affine
private def afin (v:Vec G n 1): fieldX G.ColorIndex:= fun i=> ∑ j:Axis,(i.1 j :ℤ) * (missing n *ᵥ component v i.2) (0,coord j)
lemma stink (v:Vec G n 1) : Quiet (afin v) 1:=by
     apply low_quiet; intro a; let f(j:Axis)(x:Lieu Axis):ℝ:= (missing n*ᵥ component v a) (0,coord j)*x j; refine ⟨∑ j,f j,(Flavor Axis 1).sum_mem (fun j _=> (Flavor Axis 1).smul_mem _ (flavor_position j)),fun x=>?_⟩; unfold afin; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
lemma stairs (v:Vec G n 1)(p:Cover × Shade G)(z:Site n): mountain (afin v) p=(missing n*ᵥ component v p.2.2) (z+wrap n p.1,coord p.2.1) :=by
     unfold mountain afin; dsimp only; rw [rakeM (component v p.2.2) (z+wrap n p.1) 0, ← Finset.sum_sub_distrib, Finset.sum_eq_single p.2.1]; simp; ring; intro b _ hb; simp [hb]; simp
variable {u:Train i}{N:Side}
-- altitude and fees. period origin any p
lemma HaQ {b:ℝ} {p:Script (Shade G) r}(h:p.abides)(he:4 ≤ i)(m:ℕ)(hp:soot (m+1) p b)(x:Site n)(v:Vec G n 1)(hZ: Prog K u G n *ᵥ v=0)(w:Fin r→deck (Shade G) n)(i:Fin r): scribe x p (update w i (deckW G n v))=0:=by
     have hv (j:G.ColorIndex): d 1 n *ᵥ component v j=0:=by
          have ht: Precision.K ((pink K.penalty u).acts n)*ᵥ component v j=0:=by rw [← component_mul, hZ]; rfl
          exact (curtain0 u he (K:=K) _).1 ht
     choose P hP using fun j=>origins (component v j) (hv j)
     let g:deck G.ColorIndex n:= fun p=>P p.2 (p.1,vac); let q:= afin v + upl x g
     have h1 (f:ℕ)(a:deck (Shade G) n): Quiet (upl x a) f:=⟨‖a‖,norm_nonneg _,fun j=>(norm_le_pi_norm a (x+wrap _ j.1,j.2)).trans (le_mul_of_one_le_right (norm_nonneg _) (poise_one ..))⟩
     have hr:Quiet (upl x g) 1:=⟨‖g‖,norm_nonneg _,fun j=>(norm_le_pi_norm g (x+wrap _ j.1,j.2)).trans (le_mul_of_one_le_right (norm_nonneg _) (poise_one ..))⟩; have hg: Quiet q 1:= quietAdd (stink v) hr
     have hz: upl x (deckW G n v)= mountain q :=by
          ext1 j; let i:=x+wrap n j.1; change component v j.2.2 (i,coord j.2.1)= q (j.1+step j.2.1,j.2.2)-q (j.1,j.2.2)
          rw [hP]; change _ + (d 0 n *ᵥ _ ) (i,coord j.2.1)=_; rw [d_sites]; unfold q; rw [Pi.add_apply,Pi.add_apply,add_sub_add_comm, show afin v _ - afin v _= _ from stairs v j x]; unfold upl;rw [map_add,wrap_step,←add_assoc]
     rw [← timing]; rw [show (fun t=> upl x (update w i (deckW G n v) t))= update (fun t=> upl x (w t)) i (mountain q) from ?_]; swap
     · funext j; by_cases ht:j=i
       · subst j; rw [update_self,hz,update_self]
       rw [update_of_ne ht,update_of_ne ht]
     refine crest_zero p h hp _ i q (Pi.single i 1) (by simp) (fun _ _=>h1 .. ) ?_; simpa using hg
end YM.OPE.Cascade.Paver
