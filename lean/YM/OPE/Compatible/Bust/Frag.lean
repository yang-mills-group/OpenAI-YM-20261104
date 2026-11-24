import YM.OPE.Compatible.Bust.Rag
/-!
# Cart winding; Seat Feynman normalization transport.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Matrix
open scoped Topology BigOperators Classical
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} [Fintype I] {N:Side}
def Formed (A: Row I I)(M:Mat (Tab I N)) (v:Site N): Prop:=∀ a b:Cover,∀ i j: I,M (v+wrap N a,i) (v+wrap N b,j)= A i j (b-a)
lemma hornT (M:Mat (Tab I N))(v:Site N)(A:RowB I)(h:Formed A.val M v)(x:Seat k m I) (j:ℕ):
     worldR m k v I (lapD A m k x) j= wind j • Semester M (worldR m k v I x (j+2)):=by
       let y:=lapD A m k x; let b:=lilies m k I y; let q:=lilies m k I x; have hh(t): Summable (b t):= tiller m _; let p:=q (j+2); have hp:Summable p:= tiller m _
       have ht(i:Page I (j+2)): A.val (i 0).2 (mort i 0).2 (poke i)= M (v+wrap N (i 0).1,(i 0).2) (v+wrap N (mort i 0).1,(mort i 0).2):= (h ..).symm
       let B:=tunnel A.val p
       ext1 z; rw [show worldR m k v I _ _=orchestra (b j) v from toScript m j v _,show worldR m k v I x (j+2)=orchestra p v from toScript ..,_root_.smul_apply,stanzaR, show (b j).orchestra v z=scribe v _ _ from (instruments _ (hh _) ..).tsum_eq.symm,show b j=_ from pulse_i x A _,score_scaled]; apply congr_arg (wind j*·)
       have hZ:=Tap_reads M p z v hp; let g(i:Page I (j+2)):= B i* render v (melt i) z; have hS: HasSum g (routeTap M p z v):=by
            convert! hZ using 1; funext i; unfold g B tunnel; rw [ht];rfl
       unfold scribe pad; rw [Sack.cart_bill (f:=B) melt (fun i=>render v i z) hS.summable, hS.tsum_eq]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; apply congr_arg (M i j*·); convert! (instruments p hp v (Fin.cons (deltaH i) (Fin.cons (deltaH j) z))).tsum_eq using 1; congr! 2
       · funext l; by_cases h:l=i<;>simp [deltaH,h]
       congr! 1; funext l; by_cases h:l=j<;>simp [deltaH,h]
lemma flareV {M:Mat (Tab I N)} (v:Site N)(A:RowB I)(h:Formed A.val M v)(x:Seat k m I)(r:ℝ)(t:ℕ): worldR m k v I (fixExp (lapD A m k).toLinearMap r t x) = fixExp (opus M) r t (worldR m k v I x):=by
     let u:=lapD A m k; let f:=worldR m k v I; have he(n:ℕ):f ((u.toLinearMap^n) x)=(opus M ^n) (f x):=by
          induction n with
          | zero=> rfl
          | succ n ih=>
               rw [pow_succ',pow_succ',End.mul_apply,End.mul_apply, ← ih]; exact funext (fun j=> hornT M v A h _ j)
     rw [Hflow,Hflow,map_sum]; refine sum_congr rfl (fun i _=>?_); rw [map_smul, he i]
lemma cadillac (v:Site N)(x:Seat k m I)(u:deck I N): Flair (lilies m k I x) k u v=Strike k (worldR m k v I x) u:=by
     unfold Flair Strike; refine sum_congr rfl fun i _=>?_ ; let q:= moduleAt m k i I x; rw [show worldR m k v I _ _=reading m i v q from rfl,toScript]; exact (instruments _ (tiller _ q) v _).tsum_eq
end YM.OPE.Silt.Float
