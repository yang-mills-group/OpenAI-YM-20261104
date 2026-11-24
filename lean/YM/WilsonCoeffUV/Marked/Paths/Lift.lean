import YM.WilsonCoeffUV.Marked.Paths.Spine
import YM.WilsonCoeffUV.Stable.Evaluations
/-!
# Lift on cover other-vessels derivative masses
Gauge wind tested even on periodic aliases. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open PowerSeries Gauge Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Shard Planned.PrimaryIntegral295 Place Carrier
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators
open Work.F03
variable {G:Gauge}{n:Side}{k h r:ℕ}{s A B:ℝ}

-- names of the poly

def insideP (A:Link G n): Leg G:= A ∘ (foldUnder n)
def outsideP (A:Link G n)(x:YForest G):ℝ:= - forestP A x.1 x.2.2

def comingP (A:Link G n)(x:YForest G):ℝ:= -forestP A (x.1+ step (feather x).2) x.2.2
def upward (A:Link G n): Leg G:= comingP A-outsideP A
def allS (A:Link G n): Leg G:= insideP A+upward A
lemma balanced (A:Link G n)(x:Edge Cover)(i:G.ColorIndex): allS A (stone x i) = ∑ j:wordBand G x,glisten j * (faceCurl (slotFace (bladeP j) 0) (arm G n 1 A)) i:=by
    let L:= Fountain.colorL (G:=G) i; let Q (j:wordBand G x):=faceCurl (slotFace (bladeP j) 0) (arm G n 1 A); let X:= forestP A; let Z:=X x.1; let Y:= X (x.1+step x.2)
    have hv:= congr_arg L (worth_axis A x)
    rw [map_sum,map_sub,_root_.map_add] at hv; simp only [map_smul] at hv
    change (∑ j:wordBand G x,glisten j * L (Q j))= L Z + L _ - L Y at hv
    change insideP A (stone x i)+(comingP A (stone x i)-outsideP A (stone x i))=∑ j:wordBand G x,glisten j*L (Q j)
    rw [hv]; unfold comingP; rw [feather_at]; change insideP A (stone x i) + (-L Y- -L Z)= L Z+ insideP A (stone x i)-L Y; ring
lemma wagesIn (A:Link G n): Wages (insideP A):=⟨0,‖A‖,norm_nonneg _,fun i=>by simp only [liftCost,pow_zero,mul_one]; exact norm_le_pi_norm A (foldUnder n i)⟩
lemma street_growth (A:Link G n): ∃ C:ℝ,0≤C∧∀ (x: Cover)(i:G.ColorIndex), ‖-forestP A x i‖≤C*size x:=by
    let L:G.Color→L[ℝ] Lawn G.ColorIndex:= (coatC G).symm.toContinuousLinearMap
    let a:= ‖arm G n 1 A‖
    refine ⟨‖L‖*a,mul_nonneg (norm_nonneg _) (norm_nonneg _),fun i p=>?_⟩
    rw [norm_neg]; exact (norm_le_pi_norm (L (forestP A i)) p).trans ((L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (gauge_growth ..) (norm_nonneg _)).trans_eq (by unfold a; ring)))
lemma wagesOut (A:Link G n): Wages (outsideP A):=by
    obtain ⟨C,h,hc⟩:= street_growth A; exact ⟨1,C,h,fun y=> (hc ..).trans (mul_le_mul_of_nonneg_left (by simp [liftCost]) h)⟩
lemma wagesUp (A:Link G n): Wages (upward A):=by
    obtain ⟨C,h,hc⟩:= street_growth A; refine Wages.minus ⟨1,C,h,fun y=>(hc ..).trans (mul_le_mul_of_nonneg_left ?_ h)⟩ (wagesOut A)
    unfold liftCost; rw [pow_one,add_comm]; exact_mod_cast (size_add ..).trans (le_of_eq (by rw [size_go]))
lemma wagesAll (A:Link G n): Wages (allS A):= (wagesIn A).plus (wagesUp A)
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
lemma soloP (P: Ten V (YForest G) (k+1))(v:Fin (k+1)→ Leg G)(hp:Twig 0 s B P)(h:0<s)(p:∀ i,Wages (v i))(q:Smooth P)(z:∀ x j,windsL x j P=0) (A: Link G n)(i:Fin (k+1)):
    pluck P (Function.update v i (upward A))=0:=by
    let Q : Fin (k+1)→ Leg G:= Function.update v i (outsideP A); let R:=Function.update v i (upward A)
    have he: ledger P i=0:=by funext x; simp [ledger,z]
    have ht: Twig 0 s B (ledger P i):=by rw [he]; exact Cork.zero.cost hp.1
    have hx:= pluck_profit hp h (run_q p (wagesOut A) i); have hu:= pluck_profit hp h (run_q p (wagesUp A) i); have hf:= pluck_profit ht h (run_q p (wagesOut A) i)
    trans -(pluck (ledger P i) Q)
    · apply eyeY i _ _ hu.of_norm hf.of_norm
      intro t; cases isEmpty_or_nonempty (YForest G); · simp
      next he' =>
       let Y:= ∏ j∈Finset.univ.erase i,v j (enlist i (Classical.arbitrary (YForest G)) t j)
       let a (x:Cover)(j:G.ColorIndex) := -forestP A x j; let U x j:= Y*a x j; let K:=visitJ (YForest G) i
       have hA z:(∏ j∈Finset.univ.erase i,v j (enlist i z t j))=Y:= Finset.prod_congr rfl (fun j hj=> congr_arg (v j) (remote (Finset.mem_erase.mp hj).1 t z (Classical.arbitrary _)))
       have hz (P:Ten V (YForest G) (k+1)) z: pressOn P Q (enlist i z t)=U z.1 z.2.2 • P (enlist i z t):=by unfold Q; rw [run_p,hA,enlist_it,mul_comm]; rfl
       apply tally2 i q U t _ _ ((K.summable_iff.mpr hu.of_norm).prod_factor t) ((K.summable_iff.mpr hf.of_norm).prod_factor t) _ (hz _) (((K.summable_iff.mpr hx.of_norm).prod_factor t).congr (hz P))
       intro x j d; change pressOn P R (enlist i (waive x d j) t)=_; unfold R; rw [run_p,hA,enlist_it]; congr 1; unfold upward U a; simp only [Pi.sub_apply]; unfold comingP outsideP; simp only [waive,feather_at]; change ( -forestP A (x+step d) j- -forestP _ x j)*Y= _; ring
    rw [he]; simp [pluck,pressOn]
lemma tonicP (P:Ten V (YForest G) k)(v:Fin k→ Link G n)(h:Twig 0 s B P)(hp:0<s)(p:Smooth P)(q:∀ j (e:k=j+1),∀ x c,windsL (r:=j) x c (e ▸ P)=0):
    pluck P (fun j=>allS (v j))=pluck P (fun j=>insideP (v j)):=by

    cases k with
    | zero=> rw [Subsingleton.elim (fun j=>allS (v j)) (fun j=>insideP (v j))]
    | succ k=>
       let Y (i:ℕ)(j:Fin (k+1)):= if j.val< i then allS (v j) else insideP (v j)
       have ht i j: Wages (Y i j):=by unfold Y; split; exact wagesAll _; exact wagesIn _
       have he (i:ℕ)(hx:i≤k+1): pluck P (Y i)=pluck P (Y 0):= by
          induction i with
          | zero=> rfl
          | succ i ih=>
             let u:Fin (k+1):=⟨i,by omega⟩
             have hx: Y (i+1)= Function.update (Y i) u (allS (v u)):=by
                funext j; by_cases he:j=u; · subst j; rw [Function.update_self]; exact if_pos i.lt_succ_self
                rw [Function.update_of_ne he]; unfold Y; simp only [show j.val< i+1 ↔ j.val< i from by have hh:j.val≠i:= fun x=>he (Fin.ext x); omega]
             refine Eq.trans (sub_eq_zero.mp ?_) (ih (by omega)); rw [hx,pluck_grade h hp (ht i) (wagesAll _), show Y i u= insideP (v u) from if_neg (lt_irrefl _), allS, add_sub_cancel_left, soloP P (Y i) h hp (ht i) p (q _ rfl) _ u]
       specialize he (k+1) le_rfl; rw [show Y (k+1)=(fun j=> allS (v j)) from funext fun j=>if_pos j.isLt] at he; simpa [Y] using he
end YM.WilsonCoeffUV.Mer.Rolls
