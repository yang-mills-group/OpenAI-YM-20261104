import YM.Contacts.Prairie.Motion
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
variable {X Y:Type*}
variable {S:Boom}{P:X→ℝ→ Prop}{f:Word→ X}
lemma collective {P:Y→ℝ→Prop}(s:Finset Y)(h:∀ t, Monotone (P t))(ht:∀ t∈s,∃ x≥(0:ℝ), P t x):∃ x≥(0:ℝ),∀ t∈s,P t x:= by
   induction s using Finset.induction with|empty=>exact ⟨_,show 0≤(0:ℝ) from le_rfl,by simp⟩|insert i v hi ih=>
   obtain ⟨p,hp,hk⟩:=ih (fun i hi=> ht i (mem_insert_of_mem hi)); obtain ⟨q,hq,hg⟩:=ht i (mem_insert_self ..); refine ⟨p+q,add_nonneg hp hq,fun j hj=>?_⟩; rcases mem_insert.mp hj with he|he; subst j; exact h i (le_add_of_nonneg_left hp) hg; exact h j (le_add_of_nonneg_right hq) (hk j he)
lemma bases_run (b:ℝ)(hb:0≤b)(hN: P (f []) b)(hp:∀ x,Monotone (P x))(h:∀ s∈ S,∃ t≥0,∀ p, OK S p→ ∀ v≥(0:ℝ), P (f p) v→ P (f (s::p)) (v/4+t)): Bases S P f:= by
   obtain ⟨z,hz,h⟩:= collective (P:=fun s t=> ∀ p,OK S p→ ∀ v≥(0:ℝ), P (f p) v→ P (f (s::p)) (v/4+t)) S (fun s t v ht h p hi w hw hP=> hp _ (add_le_add (le_refl _) ht) (h p hi w hw hP)) h
   refine ⟨b+4*z, by linarith, fun p he=>?_⟩; induction p with|nil=> exact hp _ (by linarith) hN|cons s p ih=> apply hp _ _ (h s he.head p he.tail _ (by linarith only [hb,hz]) (ih he.tail)); linarith
variable [Sub X]
lemma diff_run (hp:∀ x,Monotone (P x))(ht : Bases S P f) (hu:∀ a b x y,P x a→ P y b→P (x-y) (a+b))(h:∀ s∈ S,∃ x≥(0:ℝ),∀ p q u, OK S p→OK S q → OK S u → ∀ v≥(0:ℝ), P (f (u++p)-f (u++q)) v→ P (f (s::(u++p))-f (s::(u++q))) (v/4+x*mileage u)): Diff S P f:= by
   obtain ⟨z,hz,h⟩:= collective (P:=fun s x=> ∀ p q u, OK S p→OK S q→OK S u→∀ v≥(0:ℝ), P (f (u++p)-f (u++q)) v→ P (f (s::(u++p))- f (s::(u++q))) (v/4+x*mileage u)) S (fun s t w hv h p q u hi hj hk v hh hK=> hp _ (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hv (mileage_pos u).le)) (h p q u hi hj hk v hh hK)) h
   obtain ⟨p,H,hP⟩:= ht; let x:=4*z+2*p; have hx:0≤x:= (by unfold x; linarith); refine ⟨x,hx,fun i j u hi hj hk=>?_⟩; induction u with|nil=> apply hp _ _ (hu _ _ _ _ (hP i hi) (hP j hj)); rw [mileage_nil,mul_one]; unfold x; linarith|cons s u ih=>
   have hw:= mileage_pos u; apply hp _ _ (h s hk.head i j u hi hj hk.tail _ (mul_nonneg hx hw.le) (ih hk.tail)); rw [mileage_cons]; unfold x; nlinarith only [hw,H]
end Parcel
end
end YM.Contacts.Prairie
