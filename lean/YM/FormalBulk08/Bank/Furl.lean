import YM.FormalBulk08.Bank.Sandy

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {G : Gauge} {n f : Side} {S : StepData n f} {P : Patch}

abbrev Bud (P : Patch) (L : Lodge P):= {x:Site P.L × Axis// Lodge.retain P L x.1 x.2}
def shrub (T : Lodge P) (x : Bud P T) (i:G.ColorIndex) : Minor G P T := ⟨(x.val.1,coord x.val.2,i),by simp_rw [show Exterior.axisEquiv.symm (coord x.val.2)= _ from Exterior.axisEquiv.symm_apply_apply _];exact x.property⟩
variable (S)

def botanic (T : Lodge S.patch) : (T.forest (S:=S)).Free≃ Site n × Bud S.patch T where
   toFun i:= (S.ratio.parent i.val.1,⟨(S.ratio.residue i.val.1,i.val.2),fun e=>i.property ((T.repeats i.val).mpr e)⟩)
   invFun x:=⟨(S.ratio.assemble (x.1,x.2.val.1),x.2.val.2),fun h=>by
       have hp:= (T.repeats _).mp h; dsimp only at hp;rw [Ratio.assemble_res] at hp; exact x.2.property hp⟩
   left_inv i:= by apply Subtype.ext; dsimp only; rw [Ratio.assemble,S.ratio.unpack_at]
   right_inv j:= by
       apply Prod.ext
       · exact Ratio.assemble_parent S.ratio _
       apply Subtype.ext; apply Prod.ext <;> first|exact Ratio.assemble_res S.ratio (j.1,j.2.val.1)|rfl

lemma shrub_pin (T : Lodge S.patch) (x : (T.forest (S:=S)).Free) (a : G.ColorIndex) : T.splitting (S:=S) (pines (S:=S) T.forest (x,a)) = ((botanic S T x).1,shrub T (botanic S T x).2 a) := by
   apply Prod.ext
   · have he:= congr_arg Prod.fst (T.alignment (S:=S) (pines _ (x,a))); simp_rw [unitSplit,split_co] at he; exact he.symm
   apply Subtype.ext; have he:= congr_arg Prod.snd (T.alignment (S:=S) (pines _ (x,a))); simp_rw [unitSplit,split_co] at he; exact he.symm

variable {S}
-- glyph algebra compositional logarithm decomposed via powers
variable {V I : Type*}
lemma covelog_sum (p q : Pap V) (hp : coeff 0 p=1) (hq : coeff 0 q=1) : covelog (p*q)=covelog p+covelog q:= by
    have hu : p*q= expan (covelog p+covelog q):= by rw [←expan_mul (covelog_rank hp) (covelog_rank hq),expan_after hp,expan_after hq]
    rw [hu,covelog_after (by rw [map_add,covelog_rank hp,covelog_rank hq,zero_add])]
lemma covelog_savings (A : I→ Pap V) (P : Finset I) (h : ∀ i,coeff 0 (A i)=1): covelog (∏ i∈P,A i)=∑ i∈P,covelog (A i):=by
    have he (P : Finset I) : coeff 0 (∏ i∈P,A i)=1:= by simp_rw [coeff_zero_eq_constantCoeff_apply,map_prod,←coeff_zero_eq_constantCoeff_apply,h]; simp
    induction P using Finset.induction with
    | empty=> rw [Finset.sum_empty,Finset.prod_empty]; rw [←root_expan (R:=TypeR V),covelog_after (by simp)]
    | @insert a s h' ih=>rw [Finset.sum_insert h',Finset.prod_insert h',covelog_sum _ _ (h a) (he _),ih]
lemma stem_grade {R : Type*} [CommRing R] [Algebra ℚ R] : covelog (1+(X:PowerSeries R))=stem R:= by rw [covelog,add_sub_cancel_left,X_subst]
lemma log_grade {p : Pap V} (hp : coeff 0 p=1) (hf : ∀ n, MvPolynomial.IsHomogeneous (coeff n p) n) : ∀ n, MvPolynomial.IsHomogeneous (coeff n (covelog p)) n := by
   have he : PowerSeries.map (MvPolynomial.C (σ:=V)) (stem ℝ)=stem (TypeR V):= by
      -- use covelog of 1+X
      rw [←stem_grade,←stem_grade,map_covelog MvPolynomial.C (by simp),map_add,map_one,PowerSeries.map_X]
   intro n
   let z:= p-1; have hz (n) : MvPolynomial.IsHomogeneous (coeff n z) n:= by unfold z;rw [map_sub]; cases n; simp [hp,MvPolynomial.isHomogeneous_zero]; rename_i n; simpa using hf (n+1)
   have ht (m n : ℕ) : MvPolynomial.IsHomogeneous (coeff n (z^m)) n := by
      induction m generalizing n with
      | zero=> cases n <;> simp [MvPolynomial.isHomogeneous_zero,MvPolynomial.isHomogeneous_one]
      | succ m ih=> rw [pow_succ,coeff_mul]; exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i hi=> Finset.mem_antidiagonal.mp hi ▸ (ih i.1).mul (hz i.2))
   rw [covelog, show (p-1)=z from rfl,show coeff n ((stem (TypeR V)).subst z)=_ from subst_coeff (by simp only [z,map_sub,hp,coeff_zero_one,sub_self]) (stem (TypeR V)) n n le_rfl]; apply MvPolynomial.IsHomogeneous.sum _ _ _; intro i hi; rw [←he,coeff_map]; exact (ht i n).C_mul _
end YM.FormalBulk08.Bank
