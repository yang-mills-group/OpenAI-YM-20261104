import YM.OPE.Compatible.Lintel.Bling
/-! # Solder matrix diagonals; trace oriented operands precisely -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff
variable {I J X Y Z:Type}{G:Gauge}{n m c f:Side} {r d:ℕ}
namespace Script
open Page Virgin
variable [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][Fintype I][Fintype J][Fintype Z][DecidableEq Z]
namespace Stand
variable {A:Row J J} {M:Funds Z}{P:(X×Y)→L[ℝ] deck (I⊕J) n}{B:Module.Basis Z ℝ Y}{F:X×Y→ℝ}{g:X→Y}{Q:Script (I⊕J) 3}{C:Z≃Tab J n}(s:Stand A M P B F g Q C)
include s
lemma eyeTrace (p:Script (I⊕J) (r+2))(x: Fin r→deck (I⊕J) n):cityTap ((ROOT A).acts n) p x=∑ i:Z,∑ j:Z,M⁻¹ i j * library n p (Fin.cons (P (0,B i)) (Fin.cons (P (0,B j)) x)):=by
    rw [rootTap,summ_two_v C]; apply sum_congr rfl fun i _=>sum_congr rfl fun j _=> by rw [s.tariff,s.token i,s.token j]
omit s [Fintype I][Fintype J] [DecidableEq Z] in
lemma eye_parse (V H:Funds Z):(V*H).trace=∑ i:Z,∑ j:Z,V i j *H j i:=by simp only [trace,diag_apply,Matrix.mul_apply]
lemma ringQ (x:X) (hp:Whole A)(hx:Summable Q): -cityTap ((ROOT A).acts n) (cotton (ROOT A) Q Q) ![P (fieldT g x),P (fieldT g x)]=(M⁻¹ * HATCH F B (fieldU g x x)).trace:=by
    rw [s.eyeTrace,eye_parse]; rw [← sum_neg_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [← sum_neg_distrib]; refine sum_congr rfl fun j _=>?_
    rw [← mul_neg]; erw [s.cots x (0,B i) (0,B j) hp hx]; apply congr_arg; let v:=((0:X),B i); let w:=((0:X),B j); let T:= fieldU g x x; let q:= ![T,w,v]; let r:=Equiv.swap (1:Fin 3) 2; have he : ![T,v,w]= q ∘ r:=funext fun i=>by fin_cases i <;>rfl
    change iteratedFDeriv ℝ 3 F 0 ![T,v,w]= _; rw [he]; exact Analysis.sym_Jet (s.h.origin.of_le le_top) q r
lemma lineU {R:Script (I⊕J) 4} (he: Voice R P F)(v:X×Y): cityTap ((ROOT A).acts n) R ![P v, P v] = (M⁻¹ * ROACH F B v v).trace:=by
    rw [s.eyeTrace,eye_parse]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>congr_arg (M⁻¹ i j* ·) ?_ ; let w:=((0:X),B j); let c:=((0:X),B i); let a:=![c,w,v,v]; let z:=![v,v,w,c]; let r:= (Equiv.swap (0:Fin 4) 3).trans (Equiv.swap 2 1); have hz:a=z ∘ r:=funext fun i=>by fin_cases i <;>rfl
    calc
       library n R _= library n R (P ∘ a):= by rw [show Fin.cons (P _) (Fin.cons _ _)=P ∘ a from funext fun j=>by fin_cases j <;> rfl]
       _= _:= (he a).trans (show _ from hz.symm ▸ (show iteratedFDeriv ℝ 4 F 0 (z ∘ r)=_ from Analysis.sym_Jet (s.h.origin.of_le le_top) z r)) -- cast issue
-- leg swap wind cityTap after replacing 1 2
omit s [Fintype I] [Fintype J] in
lemma tapSpin (p:Script (I⊕J) 4)(x:Fin 4→deck (I⊕J) n): library n (swing (Equiv.swap (1:Fin 4) 2) p) x=library n p (x ∘ Equiv.swap (1:Fin 4) 2):= sum_congr rfl fun _ _=> rotating .. -- hp unused. s?
omit [Fintype I][Fintype J] in
lemma hatchHit (v:X×Y)(i j:Z): HATCH F B v j i= beat F B (0,B i) v j:=by
    let r:=(Equiv.swap (0:Fin 3) 2).trans (Equiv.swap (0:Fin 3) 1); let a:=((0:X),B j); let b:=((0:X),B i); let z:=![a,b,v]; change iteratedFDeriv ℝ 3 F 0 ![v,a,b]=iteratedFDeriv ℝ 3 F 0 z; rw [show ![v,a,b]=z∘ r from ?_]; exact Analysis.sym_Jet (s.h.origin.of_le le_top) ..; ext1 l; fin_cases l <;> rfl
omit [Fintype I] [Fintype J] in
lemma hatq (v:X×Y)(i j:Z): HATCH F B v j i= HATCH F B v i j:=by
    let a:=((0:X),B j); let b:=((0:X),B i); let p:=Equiv.swap (1:Fin 3) 2; let z:=![v,b,a]; change iteratedFDeriv ℝ 3 F 0 ![v,a,b]=iteratedFDeriv ℝ 3 F 0 z; rw [show ![v,a,b]=z ∘ p from funext fun i=>by fin_cases i <;> rfl]; exact Analysis.sym_Jet (s.h.origin.of_le le_top) ..
-- trace V H V H = Σ Vij Σh,H_jh * Vk? Σ X=i Y=j. orientation: cotton swap receives left H_i^T, right H_j. matrix V_hk. need transpose V symmetrical (H symmetric), desired H_jh, H_ki. Therefore V symmetrical. need hp.
lemma tapDouble (v:X×Y)(hp:Whole A)(hx:Summable Q)(hv: (M⁻¹).IsSymm):
   let T:= (ROOT (I:=I) A)
   cityTap (T.acts n) (swing (Equiv.swap (1:Fin 4) 2) (cotton T Q Q)) ![P v,P v]= (M⁻¹*HATCH F B v*M⁻¹*HATCH F B v).trace:=by
     intro T; let W:= HATCH F B v; let U:= M⁻¹; let L:= cotton T Q Q; let t:=Equiv.swap (1:Fin 4) 2
     have he (i j:Z): library n (swing t L) ![P (0,B i),P (0,B j),P v,P v]=(W*U*W) i j:=by
        let P' :=P (0,B i); let Q':= P (0,B j); change library n (swing (Equiv.swap (1:Fin 4) 2) L) ![P',Q',P v,P v]=_
        rw [tapSpin,show ![P',Q',P v,P v] ∘ t=![P',P v,Q',P v] from funext fun l=>by fin_cases l <;> rfl,s.corral (0,B i) v (0,B j) v hp hx]
        rw [Matrix.mul_assoc, Matrix.mul_apply]; unfold dotProduct; apply Finset.sum_congr rfl; intro k _; apply congr_arg₂
        · exact (s.hatchHit v i k).symm.trans (s.hatq v i k)
        change U.mulVec (beat F B (0,B j) v) k=(U*W) k j; rw [Matrix.mul_apply]; exact sum_congr rfl fun t _=> congr_arg (U k t * ·) (s.hatchHit v j t).symm
     change cityTap ((ROOT A).acts n) _ _=(U*W*U*W).trace
     rw [s.eyeTrace, show U*W*U*W= U*(W*U*W) by simp only [Matrix.mul_assoc],eye_parse]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; have hk :(W*U*W).transpose=W*U*W:=by rw [transpose_mul,transpose_mul,show W.transpose=W from Matrix.ext (fun i j=> s.hatq v i j), show U.transpose=U from hv,Matrix.mul_assoc]
     apply congr_arg; exact (he i j).trans (congr_fun (congr_fun hk j) i)
end Stand
end Script
end YM.OPE.Flume
