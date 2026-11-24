import YM.OPE.Compatible.Ingle.Soul
import YM.Next.WARD_BIN.Eqs
/-! # on and off shell counts -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent MeasureTheory RG Wilson Exterior Stationary Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open Module Silt.Float Drift Quit Quit.Jac
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Source Labels Source.Drops WardBin Prairies
open Finset
variable {G:Gauge}{k i r n d m:ℕ}
lemma Unlit (p:Label G d)(hx:p∈Grade (n,r))(h:n<r):p=0:=by
     apply Subtype.ext; ext i; change MvPolynomial.coeff i p.val=MvPolynomial.coeff _ 0; rw[MvPolynomial.coeff_zero]; by_contra ht; have hy: Finsupp.weight Labels.bidegree i=(n,r):= (Labels.pure_grade _ p).mp hx ht; have hh:= Labels.power_le i; have ht:height i=n:=by exact congr_arg Prod.fst ((Labels.weight_slot i).symm.trans hy)
     rw[hy,ht] at hh; exact (not_le.mpr h) hh
lemma paradeΛ (p:Label G d): p=∑ i: Fin (d+1),∑ j:Fin (i.val+1),gradePart (i.val,j.val) p:=by
      have he(e:Fin (d+1)): (∑ j∈range (d+1), gradePart (e.val,j) p)=∑ j:Fin (e.val+1),gradePart (e.val,j.val) p:=by
           rw [Fin.sum_univ_eq_sum_range (fun j=>gradePart (e.val,j) p) _]; exact (sum_subset (range_mono (show e.val+1≤d+1 from by omega)) fun i hi hg=> Unlit _ (gradePart_mem ..) (show e.val < i from Nat.le_of_not_gt (fun h=>hg (mem_range.mpr h)))).symm
      exact ((by simp_rw [←he]; rw [Fin.sum_univ_eq_sum_range (fun i=> ∑ j∈range (d+1),gradePart (i,j) p) _]; exact Labels.decompose p : (∑ i: Fin (d+1), ∑ j:Fin (i.val+1), gradePart (i.val,j.val) p) =p)|>.symm)
lemma WholeM (G:Gauge)(d:ℕ): Surjective (CacheM G d):=by
      intro p; let f(i:Fin (d+1))(j:Fin (i.val+1)):=gradePart (i.val,j.val) p; let x(i:Fin (d+1))(j:Fin (i.val+1)):Spired G j.val (i.val-j.val) d:=⟨f i j,by rw[show i.val-j.val+j.val=i.val from Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]; exact gradePart_mem ..⟩
      let q(i:Fin (d+1))(j:Fin (i.val+1)):= BandM i.val (Nat.le_of_lt_succ i.isLt) j G (x i j); let V:Carton G d:=fun i=>(fun j=> coordinateQ G d i.val j.val (q i j).1, fun j=>coordinateQ G d i.val j.val (q i j).2)
      have hp(i:Fin (d+1))(j:Fin (i.val+1)):Rashi j (V i)= x i j:= by rw[Rashi,show Tacts j (V i)=q i j from Prod.ext ((coordinateQ ..).symm_apply_apply _) ((coordinateQ ..).symm_apply_apply _)]; exact (BandM ..).symm_apply_apply _
      refine ⟨V,?_⟩; change (∑ i: Fin (d+1),∑ j: Fin (i.val+1),(Rashi j (V i)).val)=_; simp_rw[hp]; exact (paradeΛ p).symm
lemma Ghostly (t:Carton G d): CacheM G d t ∈ Maxwell.equationIdeal G d ↔ ∀ i:Fin (d+1),(t i).1∈ Ghost G d i.val∧(t i).2∈ Ghost G d i.val:=by
     let y:= CacheM G d t; let f(i: Fin (d+1)):=∑ j: Fin (i.val+1), (Rashi j (t i)).val; have ht(i: Fin (d+1))(p:Maxwell.TaylorTower G) : Labels.read (fun j=>Maxwell.gaugeJet (p j)) (f i).val=(master (t i).1 p:ℂ)+Complex.I * (master (t i).2 p:ℂ):=by
          unfold f master; simp only [AddSubmonoidClass.coe_finsetSum,map_sum,Complex.ofReal_sum]; rw [mul_sum, ←sum_add_distrib]; exact sum_congr rfl fun j _=> relayM .. -- possibly need x
     constructor
     · intro h i; have he:f i ∈ Maxwell.equationIdeal G d:= ?_ -- replace with Ideal
       · have hp (p:Maxwell.TaylorTower G): (master (t i).1 p:ℂ)+Complex.I * (master (t i).2 p:ℂ)=0:= (ht i p).symm.trans (Maxwell.ideal_meaning.mp he p)
         exact ⟨fun t=>by simpa using congr_arg Complex.re (hp t), fun t=> by simpa using congr_arg Complex.im (hp t)⟩
       apply Submodule.sum_mem _; intro j _; rw[← p_R j t]; exact equationPart h (by omega) (by omega)
     intro h; unfold CacheM; refine Submodule.sum_mem (p:=Maxwell.equationIdeal G d) (t:=Finset.univ) (f:=f) (fun i _=>?_); refine Maxwell.ideal_meaning.mpr fun p=>?_ ; rw [ht,show master (t i).1 p=0 from (h i).1 _,show master (t i).2 p=0 from (h i).2 _]; simp
end YM.OPE.Stroke
