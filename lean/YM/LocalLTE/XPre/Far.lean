import YM.LocalLTE.XPre.Horses
/-!
# Submenus preserving exact view
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof YM.Merge
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι: Type}{G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ K ν t u q r s b:ℝ} {A:Activities G f} {d p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations
variable {v w:ℂ}{X:Wing→Prop}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
variable {E:Config G f→ℂ} {Z: Res G f}{W : Res G c}
variable (h: Odyssey X o o' v E Z W w t u L M g φ)
include h
open Menu
set_option quotPrecheck false
variable {T:StepData c f}{N N':ι→ Leaf R}
include h
-- same turn. payload retained. Replace exactly. Signature. Cost.Predicate
lemma reprice_l (hp: ∀ i,(M i).turn=(N i).turn)(hf:∀ i U,(M i).ingredient U=(N i).ingredient U)(he:Tunes L)(hv:SoundDoor T L)(hq:SumBudget (fun i=> ‖g i‖ * load (N i)) s): Odyssey X o o' v E Z W w s u L N g φ:=by
   let A:=t
   let K (i:ι): Unit→Leaf R:= fun _=> N i; let x (_:Unit):ℝ :=1
   have hp'(i): Grouped (M i) x (K i):= by
      refine ⟨fun _=> (hp i).symm, Summable.of_finite, fun U=>?_⟩; change HasSum (fun j : Unit=> 1* _) _; simp only [one_mul]; rw [hf]; simpa only [Fintype.sum_unique] using! (hasSum_fintype (fun j=> (K i j).ingredient U))
   refine ⟨fun i=> ?_,hq,h.cost,fun U=> ?_,fun j U=>?_,fun j U=>?_⟩
   · have hv : (N i).crest=(M i).crest:=congr_arg (fun i:Wing=> i.support R) (hp i).symm; rw [hv, ← hp];exact h.member _
   · exact (h.lyric U).congr_fun (fun i=> by apply congr_arg; have he:=Menu.prose_me (K i) x (M i) (hp' i) U; simpa only [tsum_fintype,Fintype.sum_unique,K,x,Complex.ofReal_one,one_mul] using! he.tsum_eq)
   · exact (h.old j U).congr_fun (fun i=>by apply congr_arg;have he:= Menu.entry_me (K i) x (M i) (hp' i) j U; simpa only [tsum_fintype,Fintype.sum_unique,K,x,Complex.ofReal_one,one_mul] using! he.tsum_eq)
   exact (h.grants j U).congr_fun (fun i=>by apply congr_arg; have hh:= Menu.tables L x (hp' i) he hv j U; simpa only [tsum_fintype,Fintype.sum_unique,K,x,Complex.ofReal_one,one_mul] using! hh.tsum_eq)
-- finite compositions. sum over i.N plus Ni'. no changing lower.force currency paid at input.
variable [Fintype ι]
lemma shards (hp:∀ i,(M i).turn=(N i).turn)(hx:∀ i,(M i).turn=(N' i).turn)(hf:∀ i U,(M i).ingredient U=(N i).ingredient U+(N' i).ingredient U)(he:Tunes L)(hv:SoundDoor T L)(hB: (∑ i, (‖g i‖*load (N i) + ‖g i‖*load (N' i))) ≤ r) :
    Odyssey X o o' v E Z W w r u L (Sum.elim N N') (Sum.elim g g) φ:=by
   let K (i:ι)(z:Bool): Leaf R:= if z then N i else N' i; let x (_:Bool):ℝ:=1
   have hp'(i):Grouped (M i) x (K i):=by
       refine ⟨fun z=>by unfold K; split; exact (hp i).symm;exact (hx i).symm,Summable.of_finite,fun U=>?_⟩
       convert (hasSum_fintype (fun j=> x j * (K i j).ingredient U)); rw [Fintype.sum_bool];simp [K,x,hf]
   let G':= Sum.elim g g; let M':= Sum.elim N N'
   have hZ{a : Leaf R→ℂ} {t : ℂ}{y:ι→ℂ}(hh:HasSum (fun i=> y i*a (M i)) t)(ht:∀ i, a (M i)= a (N i)+a (N' i)) : HasSum (fun i=> Sum.elim y y i * a (M' i)) t:=by
       rw [← hh.tsum_eq,tsum_fintype]; simp_rw [ht,mul_add]; convert hasSum_fintype _ using 1; rw [Fintype.sum_sum_type,Finset.sum_add_distrib];rfl
   refine ⟨fun i=>?_,⟨fun i=>?_ ,Summable.of_finite,?_⟩,h.cost,fun U=> ?_,fun j U=>?_,fun j U=>?_⟩
   · cases i with
     | inl i=> exact (show o ∈ (N i).turn.support R ∧ X (N i).turn from (hp i ▸ (show o∈ (M i).turn.support R ∧ X (M i).turn from h.member _))) -- syntax cast
     | inr i=> exact (show o ∈ (N' i).turn.support R ∧ X (N' i).turn from (hx i ▸ (show o∈ (M i).turn.support R ∧ X (M i).turn from h.member _)))
   · exact mul_nonneg (norm_nonneg _) ((Leaf.profit _).trans (R.p.loMass _ _ (Leaf.profit _)))
   · rw [tsum_fintype,Fintype.sum_sum_type]; rw [Finset.sum_add_distrib] at hB;exact hB
   · refine hZ (a:=fun M=>prose M U) (h.lyric U) (fun i=> ?_); have he:= Menu.prose_me (K i) x (M i) (hp' i) U; simpa only [tsum_fintype,Fintype.sum_bool,K,x, ↓reduceIte,Bool.false_eq_true,Complex.ofReal_one,one_mul] using! he.tsum_eq.symm
   · refine hZ (a:=fun M=>entry M j U) (h.old j U) (fun i=>?_); have he:=Menu.entry_me (K i) x (M i) (hp' i) j U; simpa only [tsum_fintype,Fintype.sum_bool,K,x,↓reduceIte,Bool.false_eq_true,Complex.ofReal_one,one_mul] using! he.tsum_eq.symm
   let y i:=v*g i
   have ht := hZ (y:=y) (a:=fun M=>quoted L M j U) (h.grants j U) (fun i=>?_)
   · exact ht.congr_fun fun i=> by cases i <;>rfl
   have he':= Menu.tables L x (hp' i) he hv j U; simpa only [tsum_fintype,Fintype.sum_bool,K,x,↓reduceIte,Bool.false_eq_true,Complex.ofReal_one,one_mul] using! he'.tsum_eq.symm
end YM.LocalLTE.XPre
