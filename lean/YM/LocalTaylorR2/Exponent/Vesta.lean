import YM.LocalTaylorR2.Mesh.Flat
/-!
 # Allow polynomial growth in the local Air chart.

 For the analytical profile-removal step, functions of the untruncated
 local oscillators themselves occur. Zest bounds, even post-period, are
 not in general available. `Drifts` replaces just that piece of the bill.
 Retain **uniform neighborhood**, before any measure justification.

 All costs here either the post period enabling constant C (Drifts) or
 the polynomial in argument, in the explicit bounded-Taylor expansion.
 Never a change of supporter derivative convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Filter Function MeasureTheory Set Finset
open ConnectedActivityE6.Blaze Tensor Brush Work.G05
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {E F G Y T A B ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {k : ℕ} {x:E}

structure Drifts (p:A→ℝ) (f : A→E→F) (x:E) (k:ℕ) : Prop where
  full : ∃ C:ℝ,0≤C ∧ ∃ n:ℕ, ∀ᶠ y in 𝓝 x,∀ a, Brush k (C*p a^n) 1 (f a) y

namespace Drifts
variable {f g : A→E→F}{p:A→ℝ} (he:∀ a,1≤p a)
lemma fat (h:Zest f x k): Drifts p f x k:=by
  obtain ⟨C,hC,hp⟩:=h.post; exact ⟨C,hC,0,hp.mono fun y hy a=>by simpa only [pow_zero,mul_one] using hy a⟩
lemma join (hf:Drifts p f x k) (h:∀ᶠ i in 𝓝 x, ∀ a, f a i=g a i): Drifts p g x k:=by
  obtain ⟨C,hC,n,hf⟩:=hf.full; refine ⟨C,hC,n,?_⟩
  filter_upwards [hf,eventually_eventually_nhds.mpr h] with y hy ha a; exact (hy a).shimmy (ha.mono fun i hh=> (hh a).symm)
lemma changeP (p':A→ℝ) (hf:Drifts p f x k)(hp:∀ x, p x≤p' x) : (∀ x,0≤p x)→Drifts p' f x k:= by
  intro hv
  obtain ⟨C,hC,n,hf⟩:=hf.full; exact ⟨C,hC,n,hf.mono fun y hy a=> (hy a).climb (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hv a) (hp a) n) hC) le_rfl⟩
private lemma loans (a:A)(mu:ℝ)(hs:0 ≤ mu)(n m:ℕ)(hp:n ≤ m): (∀ a,1 ≤ p a)→ mu*(p a)^n  ≤  mu*(p a)^m := fun h=> mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (h _) hp) hs
include he
lemma more (hf:Drifts p f x k)(hg:Drifts p g x k): Drifts p (fun a y=> f a y+g a y) x k:=by
  obtain ⟨C,hC,n,h⟩:=hf.full; obtain ⟨B,hB,m,v⟩:=hg.full; refine ⟨C+B,by positivity,n+m,?_⟩
  filter_upwards [h,v] with y hy hp a
  rw [add_mul]; exact ((hy a).climb (loans a C hC _ _ (by omega) he) le_rfl).gathering ((hp a).climb (loans a B hB _ _ (by omega) he) le_rfl)
omit he
lemma opposite (hf:Drifts p f x k): Drifts p (-f) x k:=by
  obtain ⟨C,hC,n,h⟩:=hf.full; exact ⟨C,hC,n,h.mono fun i hi a=> (hi a).opposite⟩
lemma twins (B : F→L[ℝ] Y→L[ℝ] G){g:A→E→Y}(hf:Drifts p f x k)(hg:Drifts p g x k): Drifts p (fun a y=> B (f a y) (g a y)) x k:=by
  obtain ⟨C,hC,n,h⟩:=hf.full; obtain ⟨T,hT,m,v⟩:=hg.full; refine ⟨‖B‖*C*T*3^k,by positivity,n+m,?_⟩
  filter_upwards [h,v] with y hy hp a
  exact ((hy a).twins (hp a) B).trim.climb (le_of_eq (by ring)) le_rfl
lemma scaled (L:F →L[ℝ] Y)(hf:Drifts p f x k): Drifts p (fun a y=>L (f a y)) x k:=by
  obtain ⟨C,hC,n,h⟩:=hf.full; refine ⟨‖L‖*C,by positivity,n,?_⟩
  filter_upwards [h] with y hy a; rw [mul_assoc]; exact (hy a).report _ le_rfl
include he
lemma all {T : ι→ A→E→F} (S:Finset ι)(hw:∀ i∈S,Drifts p (T i) x k): Drifts p (fun a y=> ∑ i∈ S,T i a y) x k:=by
  induction S using Finset.induction_on with
  | empty => simp_rw [sum_empty]; exact fat (Zest.still _)
  | insert i s hi h=> simp_rw [sum_insert hi]; exact (hw i (mem_insert_self ..)).more he (h fun i hi=> hw i (mem_insert_of_mem hi))
lemma double {g:A→E→Y}(hf:Drifts p f x k)(hg:Drifts p g x k): Drifts p (fun a y=>(f a y,g a y)) x k:= by
  obtain ⟨C,hC,n,h⟩:=hf.full; obtain ⟨T,hT,m,v⟩:=hg.full; refine ⟨(C+T)+(C+T),by positivity,n+m,?_⟩
  filter_upwards [h,v] with y hy hh a
  rw [add_mul]; apply Brush.pair ((hy a).climb _ le_rfl) ((hh a).climb _ le_rfl)
  · have hV:=he a; exact (loans a C hC _ _ (by omega : n≤n+m) he).trans (by gcongr; simp only [le_add_iff_nonneg_right]; exact hT)
  have hV:=he a; exact (loans a T hT _ _ (by omega : m≤n+m) he).trans (by gcongr; linarith only [hC])
lemma cube {f' : A→E→(B→F)}[Fintype B](h:∀ i:B,Drifts p (fun a y=>f' a y i) x k) : Drifts p f' x k:=by
  choose C hC n ht using fun i=> (h i).full
  let N := ∑ i:B,n i; let Q:= ∑ i:B,C i; have hQ:0≤Q:=sum_nonneg fun i _=> hC i
  refine ⟨Q,hQ,N,?_⟩; filter_upwards [eventually_all.mpr ht] with y hy a; have hw := he a
  exact Brush.fold zero_le_one (by positivity) (T:=fun i y=> f' a y i) (fun i=> (hy i a).climb ((loans a _ (hC i) _ N (single_le_sum (fun _ _=> Nat.zero_le _) (mem_univ _)) he).trans (mul_le_mul_of_nonneg_right (single_le_sum (fun i _=>hC i) (mem_univ _)) (by positivity))) le_rfl)
end Drifts
end YM.LocalTaylorR2.Exponent
