import YM.LocalLTE.East.Lanes
/-! Orbit radius inward. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
lemma soundness (p n:ℕ) (E: Site c) (Z:ℝ) (g:Veil c f→ℝ) (h: let Y:= neighbors (stagnate n X.halo*B) E; SumBudget (fun i=> if traceO S R i∈ Y then g i else 0) Z) : SumBudget (fun V: Tuple H.ThinP p=> if Orchestra H ⟨p,V⟩ n ∧ E∈ Captain.reachability (H:=H) ⟨p,V⟩ then LocalLTE.Fan.Field.stock (East.docket H ⟨p,V⟩) g else 0) ((rack Z n)^(p+1)):=by
    let X₁:=neighbors (stagnate n X.halo*B) E
    let g' i:= if traceO S R i∈ X₁ then g i else 0
    let f₀ y:= if y.card≤ n then ∏ i∈y,g' i else 0; let K (T:Tuple H.ThinP p) : DiskShelf p c f:= docket H ⟨p,T⟩; let P (T:Tuple H.ThinP p):= Orchestra H ⟨p,T⟩ n ∧ E∈ Captain.reachability (H:=H) ⟨p,T⟩
    have he:SumBudget f₀ (rack Z n):= budget_grace n h; have hg:= budget_seat he (Option (Fin p)); rw [Fintype.card_option,Fintype.card_fin] at hg
    have hi : Set.InjOn K {i| P i}:= by
       intro i hi j hj he; change P _ at hi hj; funext k; exact Subtype.ext (show (i k).val=(j k).val from (hi.1.each k).lift.trans ((congrArg _ (congr_fun he k)).trans (hj.1.each k).lift.symm)) -- edit
    convert East.indicatorPull (P:=P) K hi _ hg using 1; ext i; split
    next h'=>
       unfold LocalLTE.Fan.Field.stock; apply prod_congr rfl; intro j hj; unfold f₀; rw [if_pos (show (K i j).card≤n from (h'.1.each j).received)]; exact prod_congr rfl (fun k hk=> (if_pos (show traceO S R k∈ X₁ from (neighbors_mem ..).mpr (East.speaker H _ n h'.1 j k hk E h'.2))).symm)
    next => rfl

private lemma uplink (p:ℕ) : ∃ a:ℝ,0≤a ∧ ∀ (ι' :Type) (R: ι'→ι'→Prop) (U:Option (Fin p)→ι'), |coefficient R U / (p+1).factorial| ≤ a:=by
     obtain ⟨a,hp,h⟩:= LocalLTE.Fan.Field.coefficientBound (Option (Fin p))
     refine ⟨a,hp,fun _ _ U =>?_⟩; rw [abs_div,abs_of_nonneg (by positivity : (0:ℝ)≤(p+1).factorial)]; exact (div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos _)).trans (h _ _ U)

def tonic (p:ℕ):=(uplink p).choose
def stadium (V :ℝ) (n : ℕ) := ∑ i∈ Finset.range (n+1), East.tonic i * (East.rack V n)^(i+1)
lemma ballads (p:ℕ) (U₀:Tuple H.ThinP p) :|LocalLTE.Fan.Field.speedΛ H U₀|≤East.tonic p:= (uplink p).choose_spec.2 _ _ _
lemma endowed (p:ℕ):0≤East.tonic p:= (uplink p).choose_spec.1
lemma treasury (v:ℝ)(he:0≤v)(n:ℕ):0≤East.rack v n:= Finset.sum_nonneg fun i _=> pow_nonneg he i

lemma musicHall (n:ℕ)(g:Veil c f→ℝ)(hg:∀ i,0≤g i)(q:ℝ)(x:Site c) (h: let Y:= neighbors (stagnate n X.halo*B) x; SumBudget (fun i=> if traceO S R i∈ Y then g i else 0) q):
    SumBudget (fun p:H.fragrances => if Orchestra H p n ∧ x∈ Captain.reachability p then |LocalLTE.Fan.Field.speedΛ H p.2| * LocalLTE.Fan.Field.stock (East.docket H p) g else 0) (East.stadium q n):=by
    let Z i:= East.tonic i * (East.rack q n)^(i+1)
    let I:=Finset.range (n+1); let u i:= if i∈ I then Z i else 0; have he : SumBudget u (East.stadium q n):= by
        have hz i:0 ≤ Z i:= mul_nonneg (East.endowed i) (pow_nonneg (East.treasury _ (budget_nonneg h) n) _)
        apply budget_of_sum (fun i=> by
             unfold u; split; · exact hz _
             exact le_rfl); intro s; unfold u; rw [← sum_filter]; exact sum_le_sum_of_subset_of_nonneg (fun i hi=> (mem_filter.mp hi).2) (fun i _ _=> hz _)
    apply sigma_total _ u ?_ he
    intro k; unfold u; split
    next hK =>
        have he:=budget_scale (endowed k) (soundness H k n x q g h)
        refine budget_mono he (fun i=>?_) (fun i=>?_)
        · split
          next h'=> exact mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _=> Finset.prod_nonneg fun _ _=> hg _)
          exact le_rfl
        split
        next h'=> simpa only [if_pos h'] using (mul_le_mul_of_nonneg_right (East.ballads H k i) (show 0 ≤ LocalLTE.Fan.Field.stock (East.docket H ⟨k,i⟩) g from Finset.prod_nonneg fun _ _=> Finset.prod_nonneg fun _ _=>hg _))
        next => simp
    next hK=>
       apply budget_mono (f:=fun (_:Tuple H.ThinP k)=>0) (by simp [RG.SumBudget])
       any_goals intro i; rw [if_neg (show _ from fun h:Orchestra H ⟨k,i⟩ n ∧ _ => hK (Finset.mem_range.mpr (show k<n+1 from Nat.lt_succ_of_le h.1.length)))] -- edit
section KL
variable (p:ℝ→ℝ)(hp:Rate G L 0 p)
include hp in
lemma masses (n:ℕ) : Rate G L 0 (fun x=> East.stadium (p x) n):=by
   have hh (S:Finset ℕ)(f:ℕ→ℝ→ℝ)(hf:∀ i,Rate G L 0 (f i)):Rate G L 0 fun x=>∑ i∈S, f i x:=by
      induction S using Finset.cons_induction with
      | empty=> simpa only [sum_empty] using! Rate.const (G:=G) (L:=L) 0
      | cons i b hx ih=> simp only [Finset.sum_cons]; exact (hf i).add ih
   have he: Rate G L 0 fun x=> rack (p x) n:= hh _ (fun i x=> p x^i) (fun i=> by simpa only [zero_mul] using hp.pow i)
   exact hh _ (fun i x=> tonic i*(rack (p x) n)^(i+1)) (fun i=> by simpa only [zero_mul] using! ((he.pow (i+1)).mul_left (tonic i)))
end KL
end YM.PhysicalNext.Repeat.East
