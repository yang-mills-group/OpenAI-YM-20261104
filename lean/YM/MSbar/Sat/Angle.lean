import YM.MSbar.Sat.Cash
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{p: ℝ}
open Finset YM.MSbar.Bulk SectorNext.Vacuum
lemma transit (a b v w:G.El): G.chord ((a*v)*(b*w)⁻¹) ≤ G.chord (a*b⁻¹)+G.chord (v*w⁻¹):=by
    rw [show a*v*(b*w)⁻¹=a*b⁻¹ * (b*(v*w⁻¹)*b⁻¹) by group]; exact (G.chord_triangle _ _).trans_eq (by rw [G.chord_conj])
lemma vertigo {U V:Config G n} {p:ℝ}(h:∀ i,G.chord (U i*(V i)⁻¹)≤p)(w:Walk)(x:Site n):G.chord (travel U x w*(travel V x w)⁻¹)≤ w.length*p:=by
    induction w generalizing x with
    | nil=> simp [travel]
    | cons a l ih=>
       rw [travel, travel]; apply (transit ..).trans
       have hf: G.chord (a.read U x*(a.read V x)⁻¹) ≤ p := by
          unfold Step.read; split
          next ht=>
            generalize hx:a.used x=i; rw [inv_inv]
            let v:= U i; let w:=V i; have hL : G.chord (v⁻¹*w)= G.chord (v*w⁻¹):=by
               rw [← G.chord_inv (v⁻¹*w),show (v⁻¹*w)⁻¹=w⁻¹*(v*w⁻¹)* (w⁻¹)⁻¹ by group,G.chord_conj]
            exact hL.trans_le (h i)
          exact h _
       apply (add_le_add hf (ih _)).trans_eq; simp [add_mul,add_comm]
-- card.J breadth.No schedule.
def wrath (β:ℝ):= β*(625*8*Fintype.card PlaqAxes)
lemma bare_quasi (β:ℝ)(hb:0≤ β) : Quasi (bare (G:=G) (n:=n) β) (wrath β):=by
    refine ⟨by unfold wrath; positivity,fun _=> (bare_pos ..).le, fun i V U=>?_⟩
    let W:=update V i U; let d : ℝ := G.chord (U*(V i)⁻¹); have hd:0≤d:= G.chord_nonneg _
    have hv (j): G.chord (W j*(V j)⁻¹)≤ d:=by
       by_cases hx:j=i
       · subst j; change G.chord (update V i U i * _)≤ _; simp only [update_self]; exact le_refl _
       simp only [W, update_of_ne hx,mul_inv_cancel,G.chord_one]; exact hd
    let q := fun j=>G.price (faceValue V j)-G.price (faceValue W j); let A:=halo 2 {i.1}
    have he(j : Face (Per n)): q j ≤ if j.1∈A then 8*d else 0 :=by
       unfold q; split
       next hp=>
          apply le_trans (le_abs_self _); rw [abs_sub_comm]; apply (price_compare ..).trans
          have hh : G.chord (faceValue W j*(faceValue V j)⁻¹)≤ ↑(4:ℕ)*d:=vertigo hv (square _ _) _; exact (mul_le_mul_of_nonneg_left hh zero_le_two).trans_eq (by push_cast; ring)
       next hp=>
          rw [far_face j (stitch i V U) (lt_of_not_ge (fun h=> hp (halo_spec.mpr ⟨i.1,mem_singleton_self _,h⟩))), sub_self]
    unfold bare; rw [← Real.exp_add]; apply Real.exp_monotone
    have hf: energy V - energy W ≤ 625*8*Fintype.card PlaqAxes*d:=by
       unfold energy; rw [← Finset.sum_sub_distrib]; refine (sum_le_sum (fun j _=>he j)).trans ?_; change ∑ j:Site n × PlaqAxes,_ ≤ _
       rw [Fintype.sum_prod_type,Finset.sum_comm]; dsimp only
       let f(j:Site n):ℝ:=if j∈A then 8*d else 0
       have hh: ∑ j,f j ≤ 625*(8*d):=by
          calc _ = ∑ j∈A,f j:= (Finset.sum_subset (subset_univ _) fun j _ hj=>if_neg hj).symm
               _ = A.card *(8*d):= by rw [Finset.sum_congr rfl (fun i (h:i∈A)=> show f i=8*d from if_pos h),sum_const,nsmul_eq_mul]
               _ ≤ _:= mul_le_mul_of_nonneg_right (show (A.card:ℝ) ≤ 625 by exact_mod_cast (horizon 2 i.1)) (by positivity)
       change ∑ _ : PlaqAxes, (∑ i: Site n,f i) ≤ _; rw [Finset.sum_const,card_univ,nsmul_eq_mul]
       refine (mul_le_mul_of_nonneg_left hh (show 0 ≤ (Fintype.card PlaqAxes:ℝ) by positivity)).trans_eq (by ring)
    have hz:=mul_le_mul_of_nonneg_left hf hb; change -β*energy W ≤ wrath β*d+(-β*energy V); unfold wrath; linarith only [hz]
end YM.MSbar.Heath
