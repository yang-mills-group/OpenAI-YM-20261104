import YM.OPE.Compatible.Straws.Kelp
/-!
# Jet calculus along small paths of coarse parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
local notation "Lf" => Tested.germ
open Radial ScriptJ JetS
abbrev Gael (p:ℝ→E):Prop:= ∃ k:JetS E,Reads p k
def trill (p:ℝ→E):JetS E:= if h:Gael p then h.choose else 0
namespace Gael
variable {u v:ℝ→E}{p:ℝ→F}
lemma oath (h:Gael u): Reads u (trill u):=by unfold trill; rw [dif_pos h]; exact h.choose_spec
lemma chooses {k:JetS E}(h:Reads u k):trill u=k:=((oath (Exists.intro k h))).equality h
protected lemma add (h:Gael u)(hx:Gael v): Gael (u+v):=⟨_,(oath h).sum (oath hx)⟩
protected lemma mul {u v:ℝ→ℝ}(h:Gael u)(hx:Gael v): Gael (u*v):=⟨_,(oath h).pile (oath hx)⟩
protected lemma up (h:Gael u)(f:E→L[ℝ] F): Gael (f∘u):=⟨_,(oath h).tours f⟩
lemma swept {φ: Type*}[DecidableEq φ] (s:Finset φ)(p:φ→ℝ→E)(h:∀ i,Gael (p i)): Gael (∑ i∈s,p i):=by induction s using Finset.induction_on with
     | empty=>rw [Finset.sum_empty]; exact ⟨_,Reads.constants 0⟩
     | @insert i s hs hx=>rw [Finset.sum_insert hs];exact Gael.add (h i) hx
protected lemma union (h:Gael u)(hx:Gael p): Gael fun t=>(u t,p t):=by
     let c:E→L[ℝ] E×F:=ContinuousLinearMap.inl ℝ E F; let d:F→L[ℝ] E×F:=ContinuousLinearMap.inr ℝ E F; rw [show (fun t=>_)=(c∘u)+(d∘p) by funext t; simp [c,d]]; exact Gael.add (Gael.up h _) (Gael.up hx _)
variable [FiniteDimensional ℝ E]
lemma helm (u: ℝ→E)(h: ∀ c: Dual ℝ E,Gael (c ∘ u)): Gael u:=by
     let k:= Module.finBasis ℝ E; rw [show u= ∑ i,fun t:ℝ=> k.coord i (u t) • k i by funext t; rw [Finset.sum_apply]; exact (k.sum_repr _).symm]; apply swept; exact fun i=> Gael.up (h (k.coord i)) ((ContinuousLinearMap.id ℝ ℝ).smulRight (k i))
abbrev ratioU (x:ℝ→E)(t:ℝ):E:=t⁻¹ • x t
lemma walk (x:ℝ→E)(h: ContDiffAt ℝ ∞ x 0)(h0:x 0=0): Gael (ratioU x):=by
    apply helm; intro c; let K:= LinearMap.toContinuousLinearMap c; let f:=K ∘ x; have hp: f 0=0:=by unfold f; rw [Function.comp_apply,h0,map_zero]
    have hv:= (Pawn.hill (K.contDiff.contDiffAt.comp 0 h) hp).stale (1:ℝ)
    refine ⟨_, hv.cong ?_⟩; filter_upwards with i; change c (i⁻¹ • _) = i⁻¹*f _; rw [map_smul,smul_eq_mul,smul_eq_mul,mul_one];rfl
lemma climb (p:E→ℝ)(h: Bond p)(ht:Gael u):Gael (p∘u):=by induction h with
   | keep c=>exact ⟨_,Reads.constants _⟩
   | glyph c => exact Gael.up ht (LinearMap.toContinuousLinearMap c)
   | add _ _ a b=> exact Gael.add a b
   | mul _ _ a b=> exact Gael.mul a b
lemma start (p: ScriptJ E)(hp:p.B)(h:Gael u):Gael fun t=> (p (u t)).atK t:=by
     obtain ⟨h1,h2,h3⟩:= ScriptJ.bondX hp; have ht:Gael (fun x:ℝ=>x):=⟨_,(Reads.stride (1:ℝ)).cong (Filter.Eventually.of_forall fun i=>by simp)⟩; have hv:Gael fun x:ℝ=>x^2:=⟨_,(Reads.ride (1:ℝ)).cong (Filter.Eventually.of_forall fun i=>by simp)⟩; exact Gael.add (Gael.add (climb (E:=E) _ h1 h) (Gael.mul ht (climb (E:=E) _ h2 h))) (Gael.mul hv (climb (E:=E) _ h3 h))
omit [FiniteDimensional ℝ E] in
lemma rut {k':E}{a:ℝ→E→ℝ}{p':ScriptJ E} (h:Tendsto u Lf (𝓝 k'))(hp:Bears 1 a p'): ((fun t=>a t (u t))-fun t=>(p' (u t)).atK t)=O[Lf](gradeP 3):=by
      obtain ⟨ε,c,r,he,hc,hk⟩:= hp.slope.cost; let z:=(Radial.zone (E:=E)).w; have hx:Tendsto (z ∘ u) Lf (𝓝 (z k')):= ((continuous_const.add continuous_norm).continuousAt).tendsto.comp h; let C:=z k'+1; have hv:C>0:= lt_trans (lt_of_lt_of_le zero_lt_one ((Radial.zone (E:=E)).high k')) (lt_add_one _); apply Reads.isTariff.mpr; refine ⟨c*C^r,by positivity,?_⟩; filter_upwards [hx.eventually (gt_mem_nhds (lt_add_one _)),Tested.eventually_small (show 0<ε/C by positivity)] with i (hi:z (u i)< C) ht; obtain ⟨hl,hT⟩:=ht; have H:=hk (u i) i hl ((mul_le_mul_of_nonneg_left hi.le hl.le).trans ((le_div_iff₀ hv).mp hT.le)); simp only [z] at hi; apply H.trans; change c*(Radial.zone.w _)^r*1*i^3 ≤ _; rw [mul_one]; gcongr; exact le_trans zero_le_one ((Radial.zone (E:=E)).high _)
end Gael
end YM.OPE.Libra
