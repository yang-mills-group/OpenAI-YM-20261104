import YM.OPE.Compatible.Stamen.Oak
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
-- budget C estimate.O. Use masks of bad axes
lemma lentM (v w:fieldX (Shade H))(i:Fin k): mark v w i=lent {i} v w:=by ext1 j; by_cases he:j=i<;>simp[mark,he,lent]
lemma lentP (v w:fieldX (Shade H))(i j:Fin k): markP v w i j=lent {i,j} v w:=by ext1 k; by_cases ht:k=i <;> by_cases hp:k=j<;>simp only [markP,lentM,lent]; all_goals first| rw [update_of_ne hp]; simp_all [lent]| rw [hp,update_self]; simp_all
section
variable (p:Script (Shade H) k)(hp: soot m p C)(hk: 2*(k+2) ≤ m)(hv: Quiet v 0)(w:fieldX (Shade H))
include hp hk hv
variable (h:p.abides)
include h
lemma montyp (n:ℕ)(ht:Quiet w n)(hz:n≤4): HasSum (fun i=> p i*UpLong i (alpha v) w) (∑ i:Fin k, wholeX p (mark v w i)):=by
       have hh(i):HasSum (fun a=>p a*wordX (mark (alpha v) w i) a) (wholeX p (mark v w i)):=by
            rw [lentM,lentM,←charcoal p hp (by omega) hv n _ ht _ (by simpa) h]; exact (canopy p hp (by omega) hv n _ ht _ (by simpa)).hasSum
       have ht:= hasSum_sum (s:=univ) fun i _=>hh i; simpa only [UpLong,Finset.mul_sum] using! ht
lemma montya (ht:Quiet w 2):HasSum (fun i=> p i * UpLongs i (alpha v) w) (∑ i:Fin k, ∑ j∈univ.erase i, wholeX p (markP v w i j)):=by
       have hv(a:Fin k)(z:Fin k)(hq:z≠a):HasSum (fun i=> p i*wordX (markP (alpha v) w a z) i) (wholeX p (markP v w a z)):=by
            have hh : ({a,z}:Finset (Fin k)).card=2:=(by simp [hq.symm]); simp_rw[lentP]; rw [← charcoal p hp (by omega) hv 2 _ ht _ (by omega) h]; exact (canopy p hp (by omega) hv 2 _ ht _ (by omega)).hasSum
       have hh:=hasSum_sum (s:=univ) fun i _=>hasSum_sum (s:=univ.erase i) fun j hj=> hv i j (ne_of_mem_erase hj); simpa only [UpLongs,Finset.mul_sum] using! hh
lemma priceU : wholeX (timbre ships p (k+1)) (fun _=> v)=∑ i:Fin k, wholeX p (mark v (mores v 2) i):=by
       rw[←(doReads (r:=k+1) hp (by omega) (fun _=>v) (fun _=>hv)).tsum_eq, ←(montyp p hp hk hv _ h 2 (plumQ v hv 2) (by decide)).tsum_eq]; exact tsum_congr (fun i=>congr_arg _ (atlas0 (v:=v) i).2.1)
lemma priceB : wholeX (timbre ships p (k+2)) (fun _=> v)=(∑ i:Fin k, wholeX p (mark v (mores v 3) i))+(2:ℝ)⁻¹ * ∑ i: Fin k,∑ j∈ univ.erase i,wholeX p (markP v (mores v 2) i j):=by
       apply (doReads hp hk _ (fun _=>hv)).unique; convert! ((montyp p hp hk hv _ h 3 (plumQ v hv 3) (by decide)).add ((montya p hp hk hv _ h (plumQ v hv 2)).mul_left (2:ℝ)⁻¹)) using 1; ext i; change p i*_= _+_;rw [ (atlas0 (v:=v) i).2.2]; ring
end
end YM.OPE.Silt.Phere
