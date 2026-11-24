import YM.FormalOPE.RG10.MultiGauge.Sprite
/-!
 # re-indexing point/sloped frame jets into coherent polynomial family.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory Measure PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
namespace Papers
lemma poly_tensor (n:ℕ)(L:MultilinearMap ℝ (fun _:Fin n=> E) ℝ): (fun x:E=> L (fun _=>x)) ∈ papers E:= by
 let B:= Module.finBasis ℝ E
 let J:= Fin (Module.finrank ℝ E)
 let v (p:Fin n→ J): E→ℝ := (fun _=> (L (fun i=> B (p i)))) * ∏ i:Fin n,(B.coord (p i) : E→ℝ)
 have he: (fun x:E=> L (fun _=>x)) = ∑ p: Fin n→ J, v p := by
  funext x
  conv_lhs => rhs; intro; rw [← B.sum_repr x]
  rw [MultilinearMap.map_sum, Finset.sum_apply]; apply Finset.sum_congr rfl; intro p _
  rw [L.map_smul_univ (fun i=> B.repr x (p i))]; unfold v; simp [Finset.prod_apply,mul_comm]
 rw [he]; exact (papers E).sum_mem fun p _=> (papers E).mul_mem (fixed _) ((papers E).prod_mem fun i _=> linear _)
lemma jet_poly (f:E→ℝ)(n:ℕ): jet f n ∈ papers E:= (papers E).mul_mem (fixed _) (poly_tensor n (iteratedFDeriv ℝ n f 0).toMultilinearMap)
end Papers
namespace Stack
open PowerSeries Papers Splice StationaryMarks
 def rise (f:E→ℝ): Ticket E:= PowerSeries.mk fun i=> ⟨jet f i,jet_poly f i⟩
 def reading (u:E): Permit E→ₐ[ℝ] ℝ where
  toFun a:= a.val u
  map_one' := rfl
  map_mul' _ _:=rfl
  map_zero' := rfl
  map_add' _ _:=rfl
  commutes' _:= rfl
 def read (u:E): Ticket E →+* PowerSeries ℝ:= PowerSeries.map (reading u).toRingHom
omit [FiniteDimensional ℝ E] in
lemma reading_term (u : Ticket E)(n : ℕ)(x): coeff n (read x u)= (coeff n u).val x:= by unfold read; rw [coeff_map]; rfl
omit [FiniteDimensional ℝ E] in
lemma into {A B:Ticket E}(h:∀ x:E, read x A=read x B): A=B:= by apply PowerSeries.ext; intro i; apply Subtype.ext; ext1 x; rw [←reading_term,←reading_term,h]
lemma read_rise (u:E)(f:E→ℝ)(i:ℕ): coeff i (read u (rise f))=jet f i u:= by rw [reading_term,rise,coeff_mk]
lemma read_real (f:E→ℝ) (u:E): read u (rise f)=PowerSeries.mk (fun i=>jet f i u):= by apply PowerSeries.ext; intro; simp_rw [coeff_mk,read_rise]
lemma rise_mul {f g:E→ ℝ} (hf: ContDiffAt ℝ ∞ f 0)(hg:ContDiffAt ℝ ∞ g 0): rise (f*g)= rise f * rise g:= by
 apply into; intro u; rw [map_mul]; simp_rw [read_real]; apply PowerSeries.ext; intro i; rw [coeff_mk]; exact congr_fun ((directions (hf.mul hg) u).unique ((directions hf u).prod (directions hg u))) i
lemma rise_one : rise (1:E→ℝ)=1:= by apply into; intro u; apply PowerSeries.ext; intro i; rw [read_rise,map_one]; cases i with
                                                                                                                       | zero=> simp
                                                                                                                       | succ i=> simp [jet,show (1:E→ℝ)= fun _=>1 from rfl, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _),coeff_one]
 def drop {R:Type}[CommSemiring R] (l:ℕ)(A:PowerSeries R): PowerSeries R:= mk fun i=> coeff (l+i) A
 lemma recover {R:Type}[CommSemiring R] (l:ℕ)(A:PowerSeries R)(h:∀ i<l,coeff i A = 0): X^l * drop l A=A:= by
  apply PowerSeries.ext; intro i; rw [coeff_X_pow_mul']; split
  · rename_i hl; rw [drop,coeff_mk,Nat.add_sub_cancel' hl]
  rename_i hl; exact (h _ (by omega)).symm
 lemma drop_mul {R:Type} [CommSemiring R] (l:ℕ)(A:PowerSeries R): drop l (X^l * A)=A:= by apply PowerSeries.ext; intro i; simp [drop,coeff_X_pow_mul']

 def carry : PowerSeries ℝ →+* Ticket E:= PowerSeries.map (algebraMap ℝ (Permit E))
end Stack
end YM.FormalOPE.RG10.MultiGauge
