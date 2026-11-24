import YM.XSpace.KernelPoint

/-!
# All sizes, orders of Maxwell-jet requests, bare initialization order zero
kernels with true orbit regulator. Compare costs before profile pairing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Price
open Lattice Filter Function Set Top Labels Source Source.Drops
open Next.Rank Normal Contraction Finsupp MvPolynomial Configuration Beamer Expense Asymptotics
open Cross (lag extra Centered far Rout Blank readKey)
open scoped Topology BigOperators
variable {ι X : Type*} {u : Filter ι} {g : ι → Mesh} {p q : ι → ℂ}
lemma cap_real {p : ι → ℝ} (h : Cap u p) : Cap u (fun i=>(p i:ℂ)):= by obtain ⟨c,H,h⟩:=h.bounds; refine Cap.of_bounds c (h.mono (fun i hi=>?_)); simpa using hi
private lemma cap_congr (h : Cap u p) (H : p=ᶠ[u] q): Cap u q:= IsBigO.congr' h H (EventuallyEq.refl ..)

-- combine finitely many operations keeping power rate
structure Stable (p q : ι→ℂ) (u : Filter ι) (g : ι→Mesh) : Prop where
  rate : Rate u g p q
  cap : Cap u q
namespace Stable
variable {p' q' : ι → ℂ}
lemma const (u : Filter ι) (g : ι→Mesh) (c : ℂ): Stable (fun _=>c) (fun _=>c) u g := ⟨Rate.refl _ _ _, Cap.const _ _⟩
lemma add (h : Stable p q u g) (H : Stable p' q' u g): Stable (p+p') (q+q') u g:=⟨h.rate.add H.rate,h.cap.add H.cap⟩
lemma mul (S : Stretched u g) (h : Stable p q u g) (H : Stable p' q' u g): Stable (p*p') (q*q') u g:=⟨h.rate.mul H.rate S h.cap H.cap,h.cap.mul H.cap⟩
lemma sum (F G : X → ι→ℂ) (s : Finset X) (h : ∀ i∈s,Stable (F i) (G i) u g): Stable (fun i=>∑ j∈s,F j i) (fun i=>∑ j∈s,G j i) u g:= ⟨Rate.sum _ _ _ (fun i hi=>(h i hi).rate), IsBigO.sum (fun i hi=>(h i hi).cap)⟩
end Stable

variable {A : Type*} {M N : ι → Cov X}
private lemma products (S : Stretched u g) (h : ∀ i j, Stable (fun k=>(M k).cov i j) (fun k=>(N k).cov i j) u g)
    (v : A→X) (p : Finset A): Stable (fun k=> blend (M k) 0 (glyphs v p)) (fun k=> blend (N k) 0 (glyphs v p)) u g:=by
  classical
  induction p using Finset.strongInduction with
  | H p ih =>
  by_cases H:p=∅; · subst p; simp only [glyphs,Finset.prod_empty,fresh]; exact Stable.const ..
  obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr H
  have he : p=insert i (p.erase i):= (Finset.insert_erase hi).symm
  rw [he]; simp_rw [spring _ _ _ _ (Finset.notMem_erase _ _),Pi.zero_apply,zero_mul,zero_add]
  exact Stable.sum _ _ _ (fun j _=> Stable.mul S (h (v i) (v j)) (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) (Finset.erase_ssubset hi))))
lemma full_order (S : Stretched u g) (h : ∀ i j, Stable (fun k=>(M k).cov i j) (fun k=>(N k).cov i j) u g) (p : poly X):
    Stable (fun k=>blend (M k) 0 p) (fun k=>blend (N k) 0 p) u g:=by
  classical
  suffices H : ∀ m c,Stable (fun k=> blend (M k) 0 (monomial m c)) (fun k=> blend (N k) 0 (monomial m c)) u g by rw [p.as_sum]; simp_rw [map_sum]; exact Stable.sum _ _ _ (fun i _=> H ..)
  intro m c; let R := (i : m.support) × Fin (m i.val); let a (x : R):=x.1.val
  have he: monomial m (R:=ℂ) c=c • glyphs a Finset.univ:=by rw [monomial_eq,← C_mul']; congr 1; simp [glyphs,R,a,Finsupp.prod,Fintype.prod_sigma]; apply Eq.symm; rw [Finset.prod_attach _ (fun i=> MvPolynomial.X (R:=ℂ) i ^ m i), monomial_eq,map_one,one_mul]; rfl
  rw [he]; simp_rw [map_smul]; exact Stable.mul S (Stable.const u g c) (products S h a Finset.univ)

variable {G : Gauge} {n : ℕ} (D : Initialize G) (S : Stretched u g) (x : ι → Fin n→Cover) (z : ι → Points n) (d : Fin n→ℕ)

private lemma limit_paid (hx : ∀ i j : Fin n, i ≠ j→ Rout u (fun k=> z k i-z k j)) (hv : ∀ᶠ i in u,z i∈conf _) (i j : Tag G n): Cap u (fun k=> (price d (z k)).cov i j):=by
  by_cases H : Active d i; swap
  · refine cap_congr (Cap.const u (0:ℂ)) (hv.mono fun k hk=> (inactive d hk i j H).symm)
  by_cases H' : Active d j; swap
  · refine cap_congr (Cap.const u (0:ℂ)) (hv.mono fun k hk=> ((price d (z k) (G:=G)).symm i j|>.trans (inactive d hk j i H')).symm)
  let L k:=(Maxwell.legKernel (Prayer.scans i.2) (Prayer.scans j.2) (z k i.1-z k j.1))
  by_cases h:i.1=j.1
  · apply cap_congr (Cap.const u (0:ℂ)); filter_upwards [hv] with k hk; rw [cap_test d hk _ _ H H',if_pos h]; rfl
  apply cap_congr (cap_real (p:=L) (Cross.toll (fun k=> _) (hx _ _ h) _ _)); filter_upwards [hv] with k hk; rw [cap_test d hk _ _ H H', if_neg h]

include S in
theorem kv_point (hx : ∀ i j : Fin n, i ≠ j→ Rout u (fun k=> z k i-z k j)) (hi : ∀ j, Centered u g (fun i=> x i j))
    (he : ∀ i j : Fin n, far g (fun k=> x k i) (fun k=> x k j)=fun k=>z k i-z k j) (hv : ∀ᶠ i in u,z i∈conf _) (p : ∀ i, On.Grade G (d i)) :
    Rate u g (fun k=>PowerSeries.coeff 0 (D.atTuple (g k) d (wrap (g k).p.side ∘ x k) p)) (fun k=>Maxwell.Wick.moment G (z k) (fun i=> (p i).val)):= by
  let M k:=season (g k) D d (x k); let N k:= price d (z k) (G:=G)
  have h (i j : Tag G n): Stable (fun k=>(M k).cov i j) (fun k=>(N k).cov i j) u g:=⟨blends d D S x z hx hi he hv i.1 j.1 i.2 j.2, limit_paid z d hx hv _ _⟩
  apply (full_order S h (output d p)).rate.congr
  · filter_upwards with k; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, settle]
  exact hv.mono (fun i hi=> (priced d p hi).symm)
end YM.XSpace.Price
