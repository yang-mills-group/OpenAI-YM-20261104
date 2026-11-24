import YM.OPE.Compatible.Channel.Score
/-!
# Symmetry and identity. Morphisms measured at all periods uniquely determine kernel. Only needs Summable legs, not any bounding frames.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free
open scoped Topology BigOperators Classical
variable {I:Type*} {r d j:ℕ} {T:Type*}[Fintype T]
namespace Script
open Page
variable {p q : Script T r}(h:Summable p)(hh:Summable q) {n:Side}
omit [Fintype T] in
lemma rotating (a:Equiv.Perm (Fin r))(p:Script T r)(x:Fin r→ deck T n)(y:Site n): scribe y (swing a p) x = scribe y p (x ∘ a):=by
   let E : Page T r≃Page T r:=Equiv.arrowCongr a (Equiv.refl _); unfold scribe; rw [← E.tsum_eq]; refine tsum_congr fun j=>?_ ; unfold swing; change p (E.symm (E j))*_= _; rw [E.symm_apply_apply]; apply congr_arg (fun v:ℝ=> p j*v); unfold render;  have Ht(i): E j (a i)=j i:=by change j (a.symm (a i))=_; rw [a.symm_apply_apply]
   simpa only [Ht, Function.comp_apply] using Eq.symm (Equiv.prod_comp a (fun i=> x i (y+wrap n ((E j) i).1, ((E j) i).2))) -- check simp index
lemma ordered (hg:p.sorted)(h:Summable p)(j:Site n): Tensor.Sym (orchestra p j):=by
   intro v a; rw [← (show scribe j p (v∘a)= _ from (instruments p h ..).tsum_eq),← (show scribe j p v=_ from (instruments p h ..).tsum_eq)]; rw [← rotating,hg]
lemma pointed (hg:p.Idem)(h:Summable p)(j:Side) : Tensor.Sym (∑ i:Site j,orchestra p i):=by
   intro v a; have he (p:Script T r) (h:Summable p) (w:Fin r→ deck T j): (∑ i: Site j,orchestra p i) w= library j p w:=by rw [_root_.sum_apply]; apply sum_congr rfl fun i _=> (instruments p h ..).tsum_eq.symm
   rw [he p h,he p h]; calc
      _ = library j (swing a p) v:= sum_congr rfl fun i _=> (rotating ..).symm
      _ = library j (silt (swing a p)) v:= silt_read (swing_sum p h a) _
      _ = _:=by rw [hg.2 a]
lemma bandUnique (y:Site n)(h:Summable p)(hh:Summable q)(hp:p.sorted)(hq:q.sorted) (he:∀ v, value y p v=value y q v) (x): scribe y p x=scribe y q x:=by
   let A:= orchestra p y;let B:=orchestra q y
   have he:A=B:=Tensor.ext_diag A B (ordered hp h y) (ordered hq hh y) (funext fun v=> show A (fun _=>v)=B (fun _=>v) from (instruments p h _ _).tsum_eq.symm.trans ((he v).trans (instruments q hh _ _).tsum_eq))
   exact (instruments p h _ x).tsum_eq.trans ((congr_arg (fun v:Tensor.T (deck T n) ℝ r=> v x) he).trans (instruments q hh ..).tsum_eq.symm)
lemma volumes (n:Side)(h:Summable p)(hh:Summable q)(hp:p.Idem)(hq:q.Idem)(he:∀ x, narrate n p x=narrate n q x)(x): library n p x= library n q x:=by
   let A:= ∑ i:Site n,orchestra p i;let B:=∑ i:Site n,orchestra q i
   have hv(t:Script T r)(h:Summable t)(w:Fin r→deck T n):(∑ i:Site n,orchestra t i) w = library n t w := by rw [_root_.sum_apply]; exact sum_congr rfl fun i _=> (instruments t h i _).tsum_eq.symm
   have he:A=B:=Tensor.ext_diag A B (pointed hp h n) (pointed hq hh n) (funext fun v=> (hv p h (fun _=>v)).trans ((he v).trans ((hv q hh (fun _=>v)).symm)))
   exact (hv p h x).symm.trans ((he ▸ hv q hh x) : A x=_)
include h hh
lemma home (G0:p.sorted)(G1:q.sorted){φ:Filter I}[φ.NeBot](v:I→ Side)(hv:Tendsto (fun i=>(v i).val) φ atTop)
  (hp:∀ᶠ i in φ,∀ u, value (0:Site (v i)) p u=value (0:Site (v i)) q u): p=q:=by
   funext i; exact tendsto_nhds_unique_of_eventuallyEq (lands p h i v hv) (lands q hh i v hv) (hp.mono fun i hi=> bandUnique 0 h hh G0 G1 hi _)
lemma away (G0:p.Idem)(G1:q.Idem){φ:Filter I}[φ.NeBot](v:I→ Side)(hv:Tendsto (fun i=>(v i).val) φ atTop)
  (hp:∀ᶠ i in φ,∀ u, narrate (v i) p u=narrate (v i) q u): p=q:=by
   cases r with
   | zero=> -- rank0. volume division
      obtain ⟨x,hx⟩:=hp.exists; let n:=v x; have hg : (((Fintype.card (Site n)):ℕ):ℝ)>0:= Nat.cast_pos.mpr Fintype.card_pos
      funext i; letI:Unique (Page T 0):=inferInstance; specialize hx (0:deck T n)
      have he (t:Script T 0): narrate n t 0=(↑(Fintype.card (Site n)):ℝ)* t i:=by
          have ht : ∀ j:Site n, scribe j t 0=t i:=by intro j; unfold scribe; rw [tsum_eq_single i]; simp [render]; intro x hx; exact False.elim (hx (Subsingleton.elim ..))
          change (∑ j: Site n,scribe j t _) = _; rw [Subsingleton.elim (a:=(fun _ : Fin 0=>(0:deck T n))) (b:= 0)]; simp_rw [ht]; simp
      apply mul_left_cancel₀ hg.ne'; rw [← he,← he];exact hx
   | succ d=>
      funext i; by_cases he: primary i=0; swap
      · rw [show p i=0 from not_ne_iff.mp fun h=> he (G0.1 i h),show q i=0 from not_ne_iff.mp fun h=> he (G1.1 i h)]
      refine tendsto_nhds_unique_of_eventuallyEq (lands p h i v hv) (lands q hh i v hv) (hp.mono fun j hP=> ?_); exact (centerSync p G0.1 he _).symm.trans ((volumes (v j) h hh G0 G1 hP _).trans (centerSync q G1.1 he _))
end Script
end YM.OPE.Flume
