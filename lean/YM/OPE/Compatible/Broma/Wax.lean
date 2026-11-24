import YM.OPE.Compatible.Broma.Atom
/-! # actual op stability staging. norms. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
section Brim
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup Q][NormedSpace ℝ Q]
variable {X W:M→ℝ}
omit [NormedSpace ℝ E] in lemma wealthC (v:E) : Wealth (fun _:M=>v) X 1:=⟨‖v‖,norm_nonneg _,0,fun i=>by simp⟩
omit [NormedSpace ℝ E] in lemma Brim.constant (v:E):Brim (fun _:M=>v) (fun _:M=>v) X W:=by refine ⟨wealthC _,wealthC _,?_⟩; rw [sub_self]; exact wealthZ ..
-- omit [NormedSpace ℝ E] in lemma Brim.zero (X W:M→ℝ): Brim (0:M→E) 0 X W:=by refine ⟨wealthZ ..,wealthZ ..,?_⟩; rw [sub_zero];exact wealthZ ..
omit [NormedSpace ℝ E] in lemma Brim.way (V U:I→M→E)(h:Finset I)(p:∀ i∈h,Brim (V i) (U i) X W) (hx:1≤ X)(hp:0≤W): Brim (fun i=>∑ j∈h,V j i) (fun i=>∑ j∈h,U j i) X W:=⟨wealthset h (fun i j=> V j i) (fun i h'=> (p i h').A) hx zero_le_one,wealthset h (fun i j=>U j i) (fun i h'=> (p i h').B) hx zero_le_one,by let A(j:M)(i:I):= V i j-U i j; have hh:= wealthset h A (fun i hp=> (p i hp).D) hx hp; exact (show ((fun i=>∑ j∈h,V j i)-(fun i=>∑ j∈h,U j i))=(fun i=>∑ j∈h,A i j) from funext (fun i=> (sum_sub_distrib ..).symm)) ▸ hh⟩
variable {p q:M→E→L[ℝ] F}{v u:M→F→L[ℝ] Q}
lemma Canal (h: Brim p q X W)(hp:Brim v u X W)(hx:1 ≤ X)(hv:0 ≤ W): Brim (fun i:M=> (v i) ∘L (p i)) (fun i=> (u i) ∘L (q i)) X W:=by
    let A(i):=(v i)∘L(p i); let B(i):=(u i)∘L(q i); have ht{X W:M→ℝ}{g:M→ℝ}{p:M→E→L[ℝ] F}{v:M→F→L[ℝ] Q}(h: Wealth p X W)(hp:Wealth v X g): Wealth (fun i=>(v i)∘L(p i)) X (g*W):= wealth_mul hp h (fun i=>(v i).opNorm_comp_le (p i))
    have hz:Wealth A X 1:=one_mul (1:M→ℝ) ▸ ht h.A hp.A; have hh: Wealth B X 1:= one_mul (1:M→ℝ) ▸ ht h.B hp.B; refine ⟨hz,hh,?_⟩; let U(i):=(v i-u i) ∘L(p i); let V(i):=(u i) ∘L(p i-q i); change Wealth (A-B) _ _; rw [show A-B=U+V from ?_]; apply fortSum (p:=U) (q:=V) (show Wealth U X W from mul_one W ▸ ht h.A hp.D) (show Wealth V X W from one_mul W ▸ ht h.D hp.B) hx hv
    ext i j; change v i (p i j)-u i (q i j)=(v i (p i j)-u i (p i j))+u i (p i j-q i j); rw [map_sub]; abel
omit [NormedSpace ℝ E] in lemma Brim.oneOf {p q:M→E}(h: Wealth p X 1)(hp: Wealth (p-q) X W)(hx:1 ≤ X)(hv:W ≤ 1): Brim p q X W:=by
    refine ⟨h,?_,hp⟩; have H : Wealth (p-q) X 1:=by
         obtain ⟨a,b,r,H⟩:=hp; refine ⟨a,b,r,fun i=>(H i).trans (mul_le_mul_of_nonneg_left (hv i) (mul_nonneg b (pow_nonneg (zero_le_one.trans (hx i)) _)))⟩
    convert fortSum h (fortNeg H) hx zero_le_one using 1; abel
variable [Fintype I]
lemma Wπ {D:I→Type}[∀ i,NormedAddCommGroup (D i)][∀ i,NormedSpace ℝ (D i)] {p q:M→E→L[ℝ] (∀ i,D i)}(hx:1 ≤ X)(hv:0 ≤ W)(h:∀ i:I, Brim (fun j=>ContinuousLinearMap.proj i ∘L p j) (fun j=>ContinuousLinearMap.proj i ∘L q j) X W): Brim p q X W:=by
     have he {p:M→E→L[ℝ] ((i:I)→D i)} (W:M→ℝ)(hv:0 ≤ W)(hg:∀ i:I, Wealth (fun j=> ContinuousLinearMap.proj i ∘L p j) X W): Wealth p X W:=by
          refine grantV p ?_ hx hv; refine points_we _ ?_ (fun i=>hx _) (fun i=>hv _); intro i; obtain ⟨c,hc,r,H⟩:= hg i; refine ⟨c,hc,r,fun j=>?_⟩; let s':=ContinuousLinearMap.proj i ∘L p j.1; exact (s'.le_opNorm j.2.val).trans ((mul_le_of_le_one_right (norm_nonneg _) (show ‖j.2.val‖≤1 from by exact Metric.mem_closedBall.mp j.2.property |>.trans' (dist_zero_right _|>.symm.le))).trans (H j.1))
     refine ⟨he 1 zero_le_one (fun i=>(h i).A),he 1 zero_le_one (fun i=> (h i).B), he W hv ?_⟩; intro i; convert (h i).D using 1; ext; rfl
