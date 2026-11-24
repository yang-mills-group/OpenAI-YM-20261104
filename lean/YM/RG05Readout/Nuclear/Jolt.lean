import YM.RG05Readout.Nuclear.Offer
/-!
# Step charge for pair ticket

Use no angular on bodily support. Difference-of-Taylor on one Body layer
 keeps expansion in *same stencil alphabet* (bank), repays by neighboring
 norms. Head and step price α.Personal.Spatial only. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Lattice
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type}[TopologicalSpace E]
variable {V J:Type}[Fintype V][DecidableEq V]
local notation "U"=>Cloud V
local notation "W"=> Wave V
set_option quotPrecheck false
variable (s:V→ℕ)(Ω:Set E)(C:Allow V)
variable (F:E→Wave V)(C':ℝ)(x₀:ℝ)
omit [DecidableEq V] in
lemma Stone.sub {F F':E→Wave V}(h:Stone d Ω F)(ht:Stone d Ω F'): Stone d Ω (F-F') := by
    intro i hi x; convert (h i hi x).sub (ht i hi x) using 1; funext u; exact iteratedFDeriv_sub_apply (lit (F u) _|>.contDiffAt) (lit (F' u) _|>.contDiffAt)
noncomputable def pellets (s: V→ℕ) (d D:ℕ):ℝ:= ∑ i:Column V d, mortar V d D i * ∏ j:V,latch (popV i j) (s j+2)
lemma pellets_good (D:ℕ):0 ≤ pellets s d D:= Finset.sum_nonneg fun _ _=> mul_nonneg (mortar_pos ..).le (Finset.prod_nonneg fun _ _=> (latch_pos ..).le)
abbrev triangleX (d:ℕ)(x y:U)(r t:ℝ)(p:E→Wave V)(u:E): Wave V:= chord (bundle r x) (chord (bundle t y) (package d y (p u)-package d x (p u)))
lemma inter_gold (i:Column V d)(x y:U)(r t:ℝ): chord (bundle r x) (chord (bundle t y) (joint Finset.univ (fun j=>patchShift (x j) r (popV i j))))=joint Finset.univ (fun j=> inter (x j) (y j) r t (popV i j)):=by rw [bundle,bundle,tiedC,tiedC]; rfl --maybe
lemma inter_limit (x y:E4)(r t:ℝ)(v:Body){z:E4}(hz:z∈tsupport (inter x y r t v).val) (hr:0<r)(ht:0<t): ‖z-x‖≤2*r ∧ ‖z-y‖≤2*t:=⟨pebble_live r hr _ _ (collar hz).1,pebble_live t ht _ _ (collar (collar hz).2).1⟩
local notation "N"=> (∑ i:V,(s i+2))
lemma spread (h:Stone d Ω F) (hc:0 ≤ C')(hC: Plant Ω C F x₀)
    (r t:ℝ) (x y:U)(ht:0<t)(hx:t ≤ r)(hr': r ≤ 1)(hr:r ≤ 2*t)(hrP:2*r ≤ x₀)
    (hd:∀ u∈Ω, ∀ x, ‖iteratedFDeriv ℝ (d+1) (F u).val x‖ ≤ C') (hf:‖y-x‖≤4*r)(hp:N≤d+1):
    Bouquet s Ω C (triangleX d x y r t F) (pellets s d 4 * r^(d+1-N)*C'):=by
       let X:= fun u=>package d x (F u); let Y:= fun u=>package d y (F u); let Z:= Y-X; let A:= triangleX d x y r t F; have htP:0<r:=ht.trans_le hx; let b:= pellets s d 4
       have hX(a:E): iteratedFDeriv ℝ (d+1) (Z a).val=0:= by funext w; change iteratedFDeriv ℝ _ ((Y a).val-(X a).val) _=_; rw [iteratedFDeriv_sub_apply (lit (Y a) _|>.contDiffAt) (lit (X a) _|>.contDiffAt)]; unfold Y X; rw [pol_above _ _ d.lt_succ_self,pol_above _ _ d.lt_succ_self,sub_self]; rfl -- bad n
       let T:= Column V d; let a(i:T)(u):= print (fork r x (Z u)) i; let f(i:T):=fun j:V=> inter (x j) (y j) r t (popV i j); let Y'(i:T)(u):= a i u • joint Finset.univ (f i)
       have hA: A=∑ i:Column V d,Y' i:=by
            funext u; change chord _ (chord _ (Z u))= _; nth_rw 1 [print_local _ (hX u) r htP.ne' x]; simp_rw [map_sum,map_smul,inter_gold,Finset.sum_apply]; rfl
       have hm:Stone d Ω Z:= (h.package Ω F y).sub Ω (h.package Ω F x)
       let w(i : T)(j:V):=r⁻¹^(s j+2)* latch (popV i j) (s j+2); let H:= fun i:T=>mortar V d 4 i * r^(d+1)* C'; let E':= ∑ i:T, H i*∏ j:V,w i j
       have he: E'= pellets s d 4 * r^(d+1-N)*C':=by
            unfold E' pellets; simp_rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i hi=> ?_
            unfold H w; rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum];
            have hz:r^(d+1)=r^(d+1-N)*r^N:=by rw [← pow_add, Nat.sub_add_cancel hp]
            rw [hz, inv_pow]; field_simp
       by_cases hz:∃ u∈Ω,x∈tsupport (F u).val ∨ y∈ tsupport (F u).val
       swap
       · refine Bouquet.empty.permit ?_ (mul_nonneg (mul_nonneg (pellets_good _ _) (by positivity)) hc); exact fun i hi=>by unfold triangleX; rw [zero_package F i _ (fun h₀=>hz ⟨i,hi,Or.inr h₀⟩),zero_package F i _ (fun h₀=>hz ⟨i,hi,Or.inl h₀⟩),sub_self,map_zero,map_zero];rfl
       obtain ⟨u,hΩ,hΦ⟩:= hz; rw [show triangleX d x y r t F =_ from hA,← he]; refine Bouquet.sum Finset.univ (fun i:T=>H i*∏ j:V,w i j) fun i _=> ?_
       change Bouquet s Ω C (fun x=>a i x • joint Finset.univ (f i)) _
       apply Bouquet.normalize (soft_print Ω Z _ x r hm) (c:=w i) (show ∀ u∈Ω, ‖a i u‖ ≤ H i from fun u hu=>palace r htP (F u) 4 _ _ _ hc (hd u hu) (by exact_mod_cast hf)) (mul_nonneg (mul_nonneg (mortar_pos ..).le (pow_nonneg htP.le _)) hc) (fun j=>mul_pos (pow_pos (inv_pos.mpr htP) _) (latch_pos ..))
       · intro j m hj z; rw [one_pow,one_mul]; exact (fuel _ (x j) (y j) r t (popV i j) htP ht hr hx m hj z).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_inv₀ htP|>.mpr hr') hj) (latch_pos ..).le)
       rcases hΦ with hΦ|hΦ
       · exact hC _ hΩ _ hΦ _ fun j z he=> (inter_limit (x j) (y j) _ _ (popV i j) (scaled_support (_:ℂ) (f i j) he) htP ht).1.trans hrP
       exact hC _ hΩ _ hΦ _ fun j z he=> (inter_limit (x j) (y j) _ _ (popV i j) (scaled_support (_:ℂ) (f i j) he) htP ht).2.trans (le_trans (mul_le_mul_of_nonneg_left hx zero_le_two) hrP)
end YM.RG05Readout.Nuclear
