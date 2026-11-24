import YM.OPE.Compatible.Stamen.Course
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
section
variable (v w Ω:fieldX I)
abbrev mark (i:Fin r): Fin r→ fieldX I:= Function.update (fun _=>v) i w
abbrev markP (i j:Fin r): Fin r→ fieldX I:= update (mark v w i) j w
lemma wordS (x:Page I r)(i:Fin r):wordX (mark v w i) x=w (x i)* ∏ j∈ univ.erase i,v (x j):=by
       unfold wordX; rw[← mul_prod_erase _ _ (Finset.mem_univ i),show mark v w i i =_ from update_self ..]; exact congr_arg (w (x i)*·) (prod_congr rfl fun j hj=>by rw [show mark v w i j=v from update_of_ne (ne_of_mem_erase hj) ..]) -- mortar
lemma wordB (x:Page I r) (i j: Fin r)(hp:i≠j):wordX (markP v w i j) x=w (x i)*(w (x j)* ∏ p∈ (univ.erase i).erase j,v (x p)):=by
       unfold wordX; let f:=markP v w i j; rw [← mul_prod_erase _ _ (mem_univ i),show markP v w i j i =w from by simp [markP,hp]]; apply congr_arg; rw[← mul_prod_erase _ _ (mem_erase.mpr ⟨hp.symm,mem_univ j⟩),show markP v w i j j=w from by simp[markP]]; apply congr_arg; exact prod_congr rfl fun k hk=> by rw[show markP v w i j k=v from (by unfold markP mark; rw[update_of_ne (ne_of_mem_erase hk),update_of_ne (ne_of_mem_erase (mem_of_mem_erase hk))])]
lemma sumOne (x:Page I r): spellI univ (fun i=> v (x i)) (fun i=> w (x i))=∑ i, wordX (mark v w i) x:=by
        unfold spellI; simp_rw[wordS]
lemma sumBi (x:Page I r): scrollI univ (fun i=> v (x i)) (fun i=> w (x i))=∑ i,∑ j∈univ.erase i, wordX (markP v w i j) x:=by
        unfold scrollI spellI; simp_rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j hj; exact (wordB v w x i j (ne_of_mem_erase hj).symm).symm
end
open Tensor WardBin
section pol
-- Kernel.Sh
abbrev alpha (v:fieldX (Shade H)):= mores v 1
abbrev gammaO (v:fieldX (Shade H)):= mores v 2
abbrev fluxA (v:fieldX (Shade H)):= mores v 3
abbrev UpLong (a: Page (Shade H) k)(v w:fieldX (Shade H)) :ℝ:=∑ i,wordX (mark v w i) a
abbrev UpLongs (a: Page (Shade H) k)(v w:fieldX (Shade H)) :ℝ:=∑ i,∑ j ∈ univ.erase i, wordX (markP v w i j) a
lemma atlas0 (a:Page (Shade H) k):
     wholeX (coff (ships a) k) (fun _=> v)=wordX (fun _=>alpha v) a ∧ wholeX (coff (ships a) (k+1)) (fun _=>v)=UpLong a (alpha v) (gammaO v) ∧
     wholeX (coff (ships a) (k+2)) (fun _=>v)= UpLong a (alpha v) (fluxA v)+(2:ℝ)⁻¹ * UpLongs a (alpha v) (gammaO v):=by
         let S:= chiff a v; have h:= (amassed a v).trans (robust univ (fun i=>windX v (a i)))
         rw [←pageQ,←pageQ,←pageQ]; refine ⟨congr_arg JetS.s h, (congr_arg JetS.l h).trans (sumOne (alpha v) (gammaO v) a),?_⟩; rw [show leading (k+2) _=_ from congr_arg JetS.h h]; change spellI _ (fun i=>alpha v (a i)) (fun i=>fluxA v (a i))+ _ * scrollI _ (fun i=>alpha v (a i)) (fun i=>gammaO v (a i))= _; rw [sumOne,sumBi]
end pol
end YM.OPE.Silt.Phere
