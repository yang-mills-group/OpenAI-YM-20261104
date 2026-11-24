import YM.WilsonCoeffUV.Product.I.Charge
/-!
# Zinc height ratio recurrence on same schedule
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open scoped Topology BigOperators
open PowerSeries
open Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
variable {U V:Type*}{N M k e t m n u i r z:ℕ}{A:ℝ}{G:Gauge}
-- era erasures
abbrev ScalarTrim (P: Pal ℝ U): Cost:= mk fun i=> P i 0 (fun j=>j.elim0)
def axeR (P:Era G ℝ): Era G ℝ:=(fun n=> lop (P.1 n), lop P.2)
lemma Auth.axe {P:Era G ℝ}(p:Auth k P) : Auth k (axeR P):=by
    have ht n: shellK k (axeR P|>.1 n):= shell_lop (p.span n)
    refine ⟨fun i j=>?_,ht,fun n i r=>?_,fun n=> certify (ι:=Unit) (fun _=> LinearMap.id) (fun _ _ f=> f ()) _ (ht n) (fun i=>?_)⟩
    · by_cases h:j=0; · subst j; simp only [axeR,lop,↓reduceIte]; exact Bends.zero
      simp only [axeR,lop,if_neg h]; exact p.wing ..
    · by_cases h:r=0; · subst r; simp only [axeR,lop,↓reduceIte]; exact Blue.Smooth.zero
      simp only [axeR,lop,if_neg h]; exact p.pale n i r
    intro Z I a X X' H; let Q:=P.1 n; let R:= ScalarTrim (P.1 n); have hx: rollTest (flash Q) (flash Q) 1 0:= p.safe n
    have hz : flash Q= flash (lop Q)+soil R:= by
        nth_rw 1 [lop_pres Q]; rw [←uband_flash]; exact flash_add (finite_shell (ht n)) (finite_shell (uband_length _ R 0))
    change train _ (flash (lop Q))= _; rw [hz] at hx; have hb:= hx H; rw [map_add,map_add,income,income] at hb; exact add_right_cancel hb
lemma tilt_zero [Fintype U](R:Cost)(i:ℕ)(v: Matrix U V ℝ): fade v (uband R i)=uband R i:=by
    funext j; cases j with
    | zero=> funext x; rw [Blue.fade,Fintype.sum_unique]; simp only [Finset.prod_empty,Finset.univ_eq_empty,one_smul, uband, shine_lit]
    | succ j=> funext x; simp only [Blue.fade,uband,shine_dark (show 0≠j+1 by omega),Pi.zero_apply,smul_zero,Finset.sum_const_zero]
lemma oxidize [Fintype U](R:Cost)(Q:Layers ℝ U)(p:Matrix U U ℝ) (j i:ℕ): bul p Q (uband R) j i= if j=0 then uband R i else 0:=by
   classical
   induction j using Nat.strong_induction_on generalizing i with
   | h j ih=>
     cases j with
     | zero=> rw [bul_zero,if_pos rfl]
     | succ j=>
       have hp l (h:l≤ j) (i r:ℕ)(v:0<r): bul p Q (uband R) l i r=0:= by rw [ih l (by omega)]; split; exact shine_dark (by omega); rfl
       have he Z : ravel Z Q (bul p Q (uband R)) j i=0:= by
           unfold ravel; exact Finset.sum_eq_zero fun t ht=>Finset.sum_eq_zero fun y _=>funext fun r=> arbor_zero_at Z _ _ r fun x y u=> Or.inr (hp _ (by have ht:=Finset.mem_antidiagonal.mp ht; omega) _ _ (by omega))
       rw [bul_next,he,he,show ripple p _=0 from funext fun r=>ripple_zero_at _ _ _ (hp j le_rfl i _ (by omega))]; simp
lemma rumble {c f:Side}(R:Cost)(S:StepData c f)(V:Forest S.ratio) (W:FaceRow)(Y:Matrix (Body 1 f) (Body 1 c) ℝ)(T:ChartRatio G)(P:PChart G f)(k:ℕ): reed S V W Y T P k (uband R)=uband R:=by
    funext j; let L:= srCold (uband (U:=Woods G f) R) (extractV G S V Y)
    unfold reed srShade; rw [show srCold (uband R) (extractV G S V Y)= uband R from funext fun _=>tilt_zero ..,Finset.sum_eq_single 0,bul_zero]; apply tilt_zero
    · intro b h v; rw [oxidize,if_neg v]
    · simp
lemma reset_zinc (R T:Cost): Blue.mix T (uband (U:=U) R)= uband (Bank.reel T R):=by
    funext i r; cases r with
    | zero=> funext x; rw [uband,shine_lit,reelQuote]; unfold Blue.mix; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun j hj=>by simp only [Pi.smul_apply,uband, shine_lit,pow_zero,mul_one]; exact mul_comm ..
    | succ r=> rw [uband,shine_dark (show 0≠r+1 by omega)]; apply Finset.sum_eq_zero; intro j _; rw [uband, shine_dark (show 0≠r+1 by omega),smul_zero]
lemma zinc_eye (A:Levels G){Ñ:ChartRatio G}{P: Era G ℝ}(q:m<N)(h:Auth k P)(g:G.Simple)(p:LocalRatio Ñ)(z:0<r): (verseI A Ñ m N k P).2 i r = (verseI A Ñ m N k (axeR P)).2 i r:=by
    let M:= verseI (V:=ℝ) A Ñ m N k; let U:=axeR P; let V:=M U; let Z:=M P; let B:=M (P-U); have hB: B=Z-V:=verse_lin A g q p h h.axe; have he: B.2 i r=0:=by
      refine ((Auth.verse A q g p (Auth.sub h h.axe)).wing i r).exten (Bends.zero.congr (Eventually.of_forall fun n=>?_)); let X:=ll A m; let L:=A.clock.kernel; let Y:=freeForms A N (m+1); let H:=roam A N m n; let f:= n*X.L; let T:=(story A Ñ N (m+1)).1 f; let E:= ScalarTrim (P.1 f); let C:= ratioHigh A Ñ N m
      change 0= Blue.mix C (reed (stepAt X L n) (xree X L n) Y H Ñ T k ((P-U).1 f)) i r
      have hv : P.1 f-U.1 f= uband E:= by
            have ht: P.1 f= U.1 f+uband E:= lop_pres (P.1 f); rw [ht,add_comm,add_sub_cancel_right]
      rw [show (P-U).1 f= uband E from hv,rumble,reset_zinc,uband,shine_dark (Nat.ne_of_lt z)]
    exact sub_eq_zero.mp (show Z.2 i r-V.2 i r=0 from congr_fun (congr_fun (congr_arg Prod.snd hB.symm) _) _ |>.trans he)
end YM.WilsonCoeffUV.Mer
