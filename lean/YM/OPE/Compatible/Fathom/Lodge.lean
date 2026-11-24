import YM.OPE.Compatible.Fathom.Dipper
import YM.OPE.Compatible.Fathom.Cycle
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
open Silt.Float Silt Cloud
open Finset
section cm
variable {E F:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
abbrev chorus (S:E→L[ℝ] PAD I)(Y:F→L[ℝ] PAD I): E×F→L[ℝ] PAD I:= S ∘L ContinuousLinearMap.fst ℝ E F+Y ∘L ContinuousLinearMap.snd ℝ E F
-- actually needed PAD I→ topology.
set_option linter.unusedSectionVars true in lemma churn {I E F : Type} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (A:Law E)(U:Law F)(S:E→L[ℝ] PAD I)(Y:F→L[ℝ] PAD I): chamber (united A U) (chorus S Y)= chamber A S+chamber U Y:=by
     let P:= united A U; ext i j; let B:= chorus S Y; let z: E×F:= (A.inverse (coQ S i),U.inverse (coQ Y i)); have he: P.P z=coQ B i:=by apply LinearMap.ext; intro v; change A.P (A.inverse _) v.1+U.P (U.inverse _) v.2=_; rw[A.applies,U.applies];rfl
     change coQ B j ((united A U).inverse _)=_; rw [←he,show (united A U).inverse _= _ from Law.solves P z];rfl
variable [Fintype J]
lemma sinew (A:Law E)(f:E→L[ℝ] PAD I)(M:Matrix J I ℝ): Silt.chamber A (climbs M ∘L f) = M*Silt.chamber A f*Mᵀ:=by
     let t:=climbs M ∘L f; let X:= fun j=> ∑ i,M j i • coQ f i; have he(j):coQ t j=X j :=by ext y; change (M *ᵥ f y) j= _; simp only[X,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul];rfl
     ext i j; change coQ t j (A.inverse (coQ t i))=_; rw [he,he]; unfold X; rw [map_sum, LinearMap.sum_apply, mul_apply]; refine sum_congr rfl fun k _=>?_; rw [transpose_apply,mul_apply,mul_comm,LinearMap.smul_apply, map_sum]; simp only [map_smul,smul_eq_mul]; rfl
end cm
variable (u:Train r)(h:4 ≤ r)
include h in lemma blankV (x:Vec G n 1)(hz:Health (Prog K u G n) x) (y:Vec G n 1): x ⬝ᵥ (CapeV K G u n*ᵥ y)= x ⬝ᵥ (PhV K u G n*ᵥ y):=by
     rw [CapeV,add_mulVec,dotProduct_add]; refine add_eq_left.mpr (hz _ ?_); funext i; obtain ⟨x,j,q⟩:=i; let y':=tensor G (Resolvent.missing n)*ᵥy; change component (Prog K u G n *ᵥ y') q (x,j)=0; rw [Prog,component_mul]; unfold y'; rw[component_mul]; exact congr_fun ((curtain0 u h (K:=K) _).2 (rampM _)) _
lemma winter (P:Flight i j)(h:f.val=c.val*P.L.val)(K:Sponsor G)(Q:Seasons K) (hm:Mag i j)(b u:ℝ)(V: Alps K Q i u)(he:V.gear=P.wing)(X:Medal P.patch G K.K i):
     let S:=P.visit (c:=c) (f:=f) K.K h; let T:=forest S.ratio P.odd; let U:Boxes G P.patch K.K:=⟨i,hm.1,X,V.gear⟩; let A: Matrix (Body 1 f) (Body 1 c) ℝ:= installed S.ratio (P.duo K.K.penalty).A0
     let H:= Prog K.K V.gear G f; let Mf:= Master (G:=G) S P.odd (P.duo K.K.penalty).A0; let B:=Vessel K.K P.land G c hm.2.1; let R:=(flats G c).toContinuousLinearMap; let N:= chorus (climbs Mf∘L R) (vertD S P.odd)
     ∀ g : Bid.Dir G c→AxisChart G T, ∀ t:S.Choices, licensed S P.odd U V.clip V.live A V.sky g→ ∀ Y:Rill.FibreRep S P.odd U t (i:=i) V g b, ∀ x y:Vec G f 1, Health H x→Health H y→
            x ⬝ᵥ (PhV K.K V.gear G f*ᵥ y)=x ⬝ᵥ( Silt.chamber (united B Y.L.Q) N *ᵥy):=by
          intro S T U A H Mf B R N g t hS Y x y hx hy
          have hB: Silt.chamber B R=CapeV K.K G P.land c:=(Hport K.K P.land G c hm.2.1).choose_spec.1; rw [show Silt.chamber _ _= _ from churn B Y.L.Q (climbs Mf∘L R) (vertD S P.odd),sinew B R Mf,hB, Matrix.add_mulVec, dotProduct_add,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,entrusted Mf]
          let a:= P.tangent K.K hm.2.1 (c:=c) (f:=f) h; let W:= forest S.ratio P.odd; let J:=FUND S P.odd U; have hh: J= treeMatrix G S T (pink K.K.penalty P.wing):= by change treeMatrix G S T (pink K.K.penalty V.gear)= _; rw [he]
          have ht:Health (Prog K.K P.land G c) (Mfᵀ*ᵥ x):=course S W P.wing P.land _ a.1 x (he ▸ hx); rw [blankV _ hm.2.1 _ ht,fortune,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,entrusted (FreeResolvent.insertion (plant W (G:=G)))] -- tweak count
          have hz:= rollingK (S:=S) (V:=W) (A:=(P.duo K.K.penalty).A0) (u:=P.land) (v:=P.wing) a.1 x y (show Health _ x from he ▸ hx) (show Health _ y from he ▸ hy) hm.1 hm.2.1 (hh ▸ ulk_force S P.odd U)
          rw [show FUND _ _ _=_ from hh,he]; exact hz
end YM.OPE.Cascade.Paver
