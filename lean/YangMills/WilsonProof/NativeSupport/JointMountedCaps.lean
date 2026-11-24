import YangMills.WilsonProof.NativeSupport.JointMountedTariff
import YangMills.WilsonProof.NativeSupport.JointOldClosure

/-! Strengthen the native recoding of a complete regular or dirty sheet.
The same vivid hats satisfy the inflated Offer and retain the uninflated
full support cost of the old slice, for every base marker radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Marker
open MergeProof MergeProof.Menu MergeProof.Accent Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι : Type} [DecidableEq V] {B:Census V} {G:Gauge} {f:Side} {R:Rep G f}
variable {v:V→ℝ} {d b:ℝ} {o:V→Site f} [Fintype ι] {X:ι→Support f} {F:ι→ Config G f→Poly B}

theorem mounted_caps (hv:∀ i,0<v i) {g:ι→Wing}
    (h:∀ i,F i≠0→ (g i).support R=X i ∧ (g i).blank R)
    (ht:∀ i U,F i U≠0→ (g i).qualifies R U)
    (hp:∀ i,Borne o (X i) (F i) R.p.threshold) (hx:∀ i U,(F i U).part B.quiet=0)
    (he:Towed v X F R.p.B d b) (old : Finset B.Mode) (cap : ι → B.Mode → ℝ)
    (paid : ∀ i U p, p∈old → ‖(F i U).part p‖≤cap i p) :
    ∃ (P:VividId F→ Hat B R),
    (∀ i,WKey (P i)=g i.fst ∧ (P i).s=i.2.1.val) ∧ Offer o P v R.p.B d (2*b) ∧
    (∀ i U,∑ j:{i':B.Mode // Vivid F i i'} × Bool, amount (P ⟨i,j⟩) U= F i U) ∧
    ∀ (w : V → ℝ), (∀ x,0<w x) → ∀ i (p : {s : B.Mode // Vivid F i s}),p.val∈old →
      (∑ j : Bool,sumFee (P ⟨i,p,j⟩) w*load (P ⟨i,p,j⟩).M) ≤
        2*R.p.mass (X i) (Poly.toll w p.val*cap i p.val) := by
   let A(i):= {p:B.Mode// Vivid F i p}; have hh(i) (x:A i): F i≠0:=by obtain ⟨y,hy⟩:=x.property;exact fun ht=> hy (by rw [ht];rfl)
   obtain ⟨w,hw,hW,hB⟩:=he
   choose f₀ pos price limit using hB
   let f (i:ι) (p:B.Mode):= if p∈old then min (f₀ i p) (cap i p) else f₀ i p
   have hs i U p : ‖(F i U).part p‖≤f i p := by
      unfold f; split
      next included => exact le_min (price i U p) (paid i U p included)
      exact price i U p
   have hf (i:ι) (p:B.Mode) : 0≤f i p := (norm_nonneg _).trans (hs i 1 p)
   have lower (i:ι) (p:B.Mode) : f i p≤f₀ i p := by unfold f; split; exact min_le_left _ _; rfl
   have hP (i:ι) : wordsPrice v (f i)≤w i :=
     (sum_le_sum fun p _=>mul_le_mul_of_nonneg_left (lower i p) (Poly.worth hv p).le).trans (limit i)
   have hI(i)(x:A i): 1 ≤ x.val.val.card:=by
      refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_);intro h
      obtain ⟨U,hh⟩:=x.property
      exact hh ((congr_arg ((F i U).part) (show x.val=B.quiet from Subtype.ext h)).trans (hx i U))
   obtain ⟨P,HP,HQ,Hh⟩ : ∃ (u : ∀ i,A i→ Bool→Hat B R), (∀ i p j,WKey (u i p j)=g i ∧ (u i p j).s=p.val) ∧ (∀ i p,∑ l,fare (u i p l) v = 2*(Poly.toll v p.val*f i p.val))∧∀ i p U,∑ l,amount (u i p l) U=Poly.send p.val ((F i U).part p.val):=by
      have he i (p:A i): UsesFinal R.p.threshold ((g i).support R) (fun U=> (F i U).part p.val):= (h i (hh i p)).1.symm ▸ (fun U V hx ht=> congr_arg (fun f:Poly B=> f.part p.val) ((hp i).home U V hx ht))
      choose u hu hU hT using fun i p=> Menu.couple (R:=R) (g i) (s:=(p:A i).val) (fun U=> (F i U).part p.val) v (he i p) (fun U hv=> ht i U (fun h=> hv (by rw [h];rfl))) (h i (hh i p)|>.2) (hp i|>.me _) (fun t U=> congr_arg (fun f:Poly B=> f.part p.val) ((hp i).turns t U)) (fun U=> hs i U _) (Finset.card_pos.mp (show 0 < p.val.val.card from hI i p))
      exact ⟨u,hu,hU,hT⟩
   let P' (i:VividId F): Hat B R:= P i.1 i.2.1 i.2.2
   have hz i (j:A i×Bool): (P' ⟨i,j⟩).M.crest=X i:=by rw [show (P' ⟨i,j⟩).M.crest=(g i).support R from congr_arg (fun i:Wing=>i.support R) (HP i j.1 j.2).1]; exact (h i (hh i j.1)).1
   refine ⟨P',fun i=>HP ..,⟨fun i=>?_,fun i=>?_⟩,?_,?_⟩
   · rcases i with ⟨i,j⟩; rw [hz,show (P' ⟨i,j⟩).s=j.1.val from (HP ..).2]; exact (hp i).place _ _ j.1.property.choose_spec
   · refine ⟨fun i=>?_,Summable.of_finite,?_⟩
     · dsimp only; split; exact mul_nonneg (Crew v hv) (Real.exp_pos _).le;rfl
     apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap (hW i) univ) zero_le_two)
     rw [tsum_fintype,Fintype.sum_sigma, Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; dsimp only
     by_cases hx:i∈X j
     · let Z:= Real.exp (d*coverNumber R.p.B (X j)); have hN(y : A j × Bool):
           (if i∈ (P' ⟨j,y⟩).M.crest then fare (P' ⟨j,y⟩) v*Real.exp (d*coverNumber R.p.B (P' ⟨j,y⟩).M.crest) else 0)= Z*fare (P j y.1 y.2) v:=by rw [if_pos (show i∈ _ from hz j y|>.symm ▸ hx), hz]; exact mul_comm ..
       rw [if_pos hx,Finset.sum_congr rfl (fun i _=>hN i), ← mul_sum,Fintype.sum_prod_type]; simp_rw [HQ]; rw [← Finset.mul_sum];
       have hu : ∑ i : A j, Poly.toll v i.val*f j i.val≤w j:=by
          rw [← Finset.sum_subtype (p:=Vivid F j) ((univ:Finset B.Mode).filter fun p=> Vivid F j p) (fun i=>by simp) (fun i=> Poly.toll v i*f j i)]; exact (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _=> mul_nonneg (Poly.worth hv _).le (hf ..)).trans (hP j)
       refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu zero_le_two) (Real.exp_pos _).le).trans_eq ?_; ring
     rw [if_neg hx,mul_zero,sum_eq_zero]; intro y _; exact if_neg ((hz j y).symm ▸ hx) -- cast
   · intro i U
     rw [Fintype.sum_prod_type]; simp_rw [P',Hh];
     conv_rhs => rw [← Poly.studs (F i U)]
     classical
     refine (sum_subtype (p:=Vivid F i) (s:= Finset.univ.filter (Vivid F i)) (fun i=>by simp) (fun j=>Poly.send j ((F i U).part j))).symm.trans (sum_subset (subset_univ _) fun j _ h=> ?_)
     have he: (F i U).part j=0:=Classical.byContradiction fun H=> h (mem_filter.mpr ⟨mem_univ _,(show Vivid F i j from ⟨U,H⟩)⟩); simp [he]
   · intro base posBase i p member
     let raw := ∑ j : Bool,‖(P i p j).charge‖*(P i p j).M.weight
     have fprice (w' : V→ℝ) : (∑ j : Bool,fare (P i p j) w')=Poly.toll w' p.val*raw := by
       rw [show Poly.toll w' p.val*raw = ∑ j:Bool,Poly.toll w' p.val*(‖(P i p j).charge‖*(P i p j).M.weight) by simp only [raw,Finset.mul_sum]]
       apply sum_congr rfl
       intro j _
       rw [Menu.fare,Menu.sumFee,(HP i p j).2,mul_assoc]
     have bill := HQ i p
     rw [fprice] at bill
     have val : raw=2*f i p.val :=
       mul_left_cancel₀ (Poly.worth hv p.val).ne' (bill.trans (by ring))
     let E := Real.exp (R.p.supportExponent*coverNumber R.p.B (X i))
     have Epos : 0≤E := (Real.exp_pos _).le
     calc _ = E*(∑ j:Bool,fare (P i p j) base) := by
                rw [mul_sum]; apply sum_congr rfl; intro j _
                change sumFee (P i p j) base*(Real.exp (_*coverNumber _ (P' ⟨i,p,j⟩).M.crest)*(P i p j).M.weight)=_
                rw [hz]; unfold E Menu.fare; ring
          _ = 2*R.p.mass (X i) (Poly.toll base p.val*f i p.val) := by
                rw [fprice,val]; unfold E BudgetPoint.mass; ring
          _ ≤ _ := by
                unfold BudgetPoint.mass
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left ((if_pos member : f i p.val=_).trans_le (min_le_right _ _)) (Poly.worth posBase _).le) Epos) zero_le_two

end YM.Integration.InletSusceptibility.JointShadow
