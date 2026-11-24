import YM.XSpace.Influence
import YM.XSpace.NormStab
import YM.Euclid.Test

/-!
# Rapid `Test`s witness the finite detecting rank

Projection onto real Lie algebra: may test complex labels & shape tests by
extracting real and imaginary coordinates. E chart distances only refer to
separation even in finite compact-metric systems. Derivative computed on this
response.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ} {E:Type} [AddCommMonoid E] [Module ℂ E]

abbrev Correl (G:Gauge) (d:ℕ) (E:Type) [AddCommMonoid E] [Module ℂ E] := (n:ℕ)→ Test n →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n=> Sec G d) E
abbrev Prediction (G:Gauge) (d:ℕ) := Correl G d ℂ

theorem smooths (p : Fin n→Sec G d): ContinuousOn (fun x=> scene x d p) (conf n):= fun _ hx=> ((moment_smooth _ hx).continuousAt).continuousWithinAt

def forum (t:Test n) (d:ℕ): MultilinearMap ℂ (fun _ : Fin n=> Sec G d) ℂ:= by
  refine MultilinearMap.mk' (fun v=> t.applyTo (fun x=> scene x d v)) ?_ ?_
  · intro v i a b; unfold Test.applyTo; simp_rw [MultilinearMap.map_update_add,mul_add]; exact integral_add (t.smearing (smooths _)) (t.smearing (smooths _))
  intro v i a b; unfold Test.applyTo; simp_rw [MultilinearMap.map_update_smul,smul_eq_mul, fun x=>mul_left_comm (t x) a,integral_const_mul]

def reference (G:Gauge) (d:ℕ) : Prediction G d:= fun n => {
  toFun t:=forum t d
  map_add' t u:= by
    apply MultilinearMap.ext; intro v; change (t+u).applyTo _=_ + _
    unfold Test.applyTo; simp_rw [add_apply, add_mul]; rw [integral_add (t.smearing (smooths v)) (u.smearing (smooths v))]; rfl
  map_smul' a v:= by
    apply MultilinearMap.ext; intro t; change (a • v).applyTo _= a * v.applyTo _; unfold Test.applyTo; simp_rw [smul_apply,smul_eq_mul,mul_assoc]; rw [integral_const_mul] }
lemma reflects (t:Test n) (p:Fin n→ Sec G d) : reference G d n t p=t.applyTo (fun x=> scene x d p):=rfl

variable (T:FieldEnd G d) (i:Fin n)
private def arm := update (fun _ : Fin n=> LinearMap.id (R:=ℂ) (M:=Sec G d)) i T
private lemma arms (v: Fin n→Sec G d): (fun j=> arm T i j (v j))=update v i (T (v i)):=by funext j; by_cases h:j=i <;> simp [arm,h]
private def derv (Q: MultilinearMap ℂ (fun _ : Fin n=> Sec G d) E):=∑ i:Fin n,Q.compLinearMap (arm T i)
lemma arrow_field (Q: MultilinearMap ℂ (fun _ : Fin n=> Sec G d) E) (v: Fin n→ Sec G d) : derv T Q v=∑ i,Q (update v i (T (v i))):=by simp only [derv,sum_apply, MultilinearMap.compLinearMap_apply]; simp_rw [arms]
private def breeze (U:Correl G d E): Correl G d E:=fun n=> {
  toFun t:= derv T (U n t)
  map_add' x y:=by ext1 v; rw [arrow_field,map_add]; simp only [add_apply, arrow_field,Finset.sum_add_distrib]
  map_smul' t x:=by ext1 v; rw [arrow_field,map_smul]; simp only [smul_apply,arrow_field,Finset.smul_sum,RingHom.id_apply] }

def varies (Q:Correl G d E): FieldEnd G d →ₗ[ℂ] Correl G d E where
  toFun F:= breeze F Q
  map_add' A B:= by ext n t p; change derv (A+B) (Q n t) p= derv A (Q n t) p+derv B (Q n t) p; simp_rw [arrow_field,LinearMap.add_apply,MultilinearMap.map_update_add, Finset.sum_add_distrib]
  map_smul' z A:= by ext n t p; change derv (z • A) (Q n t) p=z • derv A (Q n t) p; simp_rw [arrow_field,LinearMap.smul_apply,MultilinearMap.map_update_smul,Finset.smul_sum]
lemma variation (Q:Correl G d E) (t:Test n) (p:Fin n→ Sec G d): varies Q T n t p=∑ i,Q n t (update p i (T (p i))):=arrow_field ..

lemma measures_gradient (t:Test n) (p: Fin n→ Sec G d):
    varies (reference G d) T n t p=t.applyTo (fun x=> ∑ i,scene x d (update p i (T (p i)))):=by
  rw [variation]; simp_rw [reflects,Test.applyTo, Finset.mul_sum, integral_finsetSum _ (fun i _=> t.smearing (smooths _))]

-- square real condition against complex multilinear arrays
structure Window (G:Gauge) (d:ℕ) where
  n:ℕ
  t:Test n
  p:Fin n→Sec G d

def watch (v:Window G d): Prediction G d→ₗ[ℝ] ℂ where
  toFun P:= P v.n v.t v.p
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def gradient (G:Gauge) (d:ℕ) := ((varies (reference G d)).restrictScalars ℝ) ∘ₗ (Change G d).subtype
lemma witnesses (T:Change G d) (g:G.Simple) (h:∀ w:Window G d,watch w (gradient G d T)=0): T=0:=by
  apply normstab g T; rw [genre]; intro n x hx v; refine Test.weak_null (K:=fun x=> ∑ i,scene x d (update v i (T.val (v i)))) ?_ |>.1 ?_ hx
  · refine continuousOn_finsetSum _ (fun i _=>smooths _)
  intro f; rw [← measures_gradient]; exact h ⟨n,f,v⟩
structure Cut (V:Submodule ℝ (Change G d)) where
  n:ℕ
  w:Fin n→ Window G d
  read: (Fin n→ℂ)→ₗ[ℝ] V

def Cut.diagnostic {V:Submodule ℝ (Change G d)} (K:Cut V):Prediction G d→ₗ[ℝ] V:= K.read ∘ₗ LinearMap.pi (fun i=> watch (K.w i))
def Cut.Measures {V:Submodule ℝ (Change G d)} (K:Cut V):= ∀ v:V,K.diagnostic (gradient G d v.val)=v

-- keep finite family retaining injectivity. Inspired by Extra/FD row lemma
private lemma finalists {E I:Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (L:I→ E→ₗ[ℝ]ℂ):
    ∃ s : Finset I, ∀ x,(∀ i∈s,L i x=0) → ∀ i,L i x=0:=by
  let U (s:Finset I):= ⨅ i:s, LinearMap.ker (L i.val)
  have he : ∃ n:ℕ,∃ s,Module.finrank ℝ (U s)=n:= ⟨_,∅,rfl⟩
  obtain ⟨s,hs⟩:= Nat.find_spec he; refine ⟨s,fun x hx i=>?_⟩
  have hL: U (insert i s)≤ U s:=le_iInf fun k=> iInf_le_of_le (⟨k.1,Finset.mem_insert_of_mem k.2⟩:(insert i s: Finset I)) le_rfl
  have hu:= Submodule.eq_of_le_of_finrank_le hL (hs ▸ Nat.find_min' he (show ∃ t:Finset I,Module.finrank ℝ (U t)=Module.finrank ℝ (U (insert i s)) from ⟨_,rfl⟩))
  have hh:x∈ U (insert i s):= by rw [hu]; exact (Submodule.mem_iInf _).mpr fun j=> LinearMap.mem_ker.mpr (hx j.1 j.2)
  exact LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hh ⟨i,Finset.mem_insert_self ..⟩)
lemma choose_window (g:G.Simple) (V:Submodule ℝ (Change G d)):∃ K:Cut V,K.Measures:=by
  obtain ⟨s,h⟩:= finalists (fun i : Window G d=> (watch i) ∘ₗ gradient G d ∘ₗ V.subtype)
  let e:= Fintype.equivFin s; let n:=Fintype.card s; let w (i:Fin n):Window G d:= (e.symm i).val; let X:=LinearMap.pi (fun i:Fin n=> (watch (w i)) ∘ₗ gradient G d ∘ₗ V.subtype)
  have he: LinearMap.ker X=⊥:=by
    apply le_antisymm _ bot_le; intro v hv; apply (Submodule.mem_bot ..).mpr; apply Subtype.ext; refine witnesses _ g (h v (fun i hi=>?_))
    let a:s:=⟨i,hi⟩; have hh:= congr_fun (LinearMap.mem_ker.mp hv) (e a)
    change watch (w _) (gradient G d v.val)=0 at hh; simp_rw [w,e.symm_apply_apply] at hh; exact hh
  exact ⟨⟨n,w,X.leftInverse⟩, fun x=> LinearMap.leftInverse_apply_of_inj he x⟩
end YM.XSpace.Normalize
