import YM.Integration.WilsonIndependentCollarSeedOrdinary

/-! Rooted positive-width enrollment before the collar supplies every
ordinary absolute entrance.  The price depends only on the fixed roster and strip. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarSeedTariff
open Function Finset Lattice RG Wilson Precision Work.F08
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonIndependentCollarSeedProduct
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ} {e:ℕ}

theorem original (G:Gauge) (D k:ι→ℕ) (e:ℕ):
  ∃ C:ℝ,1≤C ∧ ∀(Y:Outerm G D),Wellness k Y →
    ∀ A:ℝ,0≤A → (∀ y S,shingled y S Y e 1 A) →
    ∀ y (S:Finset ι),S.Nonempty → ∀f:Pen D S →L[ℝ] ℝ,‖f‖≤1 →
      Saturation e 0 0 (tuftV f (levelsO (Y y) S)).2 0 ((C*A)^S.card):=by
  let K:=mass k univ+e
  let co (S:Finset ι):=WilsonIndependentCollarSeedOrdinary.cost D G e K S
  have cp(S:Finset ι):0≤co S:=WilsonIndependentCollarSeedOrdinary.nonneg ..
  let C:=1+∑ S,co S
  have cOne:1≤C:=le_add_of_nonneg_right (Finset.sum_nonneg fun j _=>cp j)
  have hi(S:Finset ι):co S≤C:=(Finset.single_le_sum (fun j _=>cp j) (mem_univ S)).trans
    (by dsimp [C];linarith)
  let T:=1+∑j∈Finset.range (K+1),|tiePay (Hooks G) j 1|
  have tOne:1≤T:=le_add_of_nonneg_right (Finset.sum_nonneg fun j _=>abs_nonneg _)
  have toll(r:ℕ)(rK:r≤K):tiePay (Hooks G) r 1≤T:=(le_abs_self _).trans
    ((Finset.single_le_sum (fun j _=>abs_nonneg (tiePay (Hooks G) j 1))
      (show r∈Finset.range (K+1) by simp;omega)).trans (by dsimp [T];linarith))
  refine ⟨C*T,one_le_mul_of_one_le_of_one_le cOne tOne,?_⟩
  intro Y w A hA acct y S hs f unit i ie r _
  by_cases rK:r≤K
  · have inventory (J:Finset ι)(live:J.Nonempty):Total e K (Y y J).2 ((T*A)^J.card):=by
      intro a ae b bm
      obtain ⟨u,hu⟩:=live
      have leg:=WilsonIndependentCollarCompletePrint.cover (acct y J a ae b) hu (by norm_num : (0:ℝ)<1) (by norm_num)
      apply invoice.mpr
      have bay:SumBudget (fun x=>‖(Y y J).2 a b x‖) (A^J.card*tiePay (Hooks G) b 1):=by
        have E:WilsonIndependentCollarCompletePrint.printed Bank.terrain y J 0 ((Y y J).2 a b)=
          fun x=>‖(Y y J).2 a b x‖:=by funext x;simp [WilsonIndependentCollarCompletePrint.printed]
        simpa only [E,sub_zero] using leg
      refine ⟨bay.1,bay.2.1,bay.2.2.trans ?_⟩
      rw [mul_pow,mul_comm];exact mul_le_mul_of_nonneg_right ((toll _ bm).trans
        (le_self_pow₀ tOne (Finset.card_ne_zero.mpr ⟨u,hu⟩))) (pow_nonneg hA _)
    have sheer:=WilsonIndependentCollarSeedOrdinary.original (Y y) (T*A) (by positivity) inventory S i ie r rK
    have h:=sheer.touch f (by norm_num)
    change Fruit 0 0 0 (f ∘ (levelsO (Y y) S).2 i r) _
    apply h.more
    have z:=mul_le_mul_of_nonneg_right ((hi S).trans (le_self_pow₀ cOne (Finset.card_ne_zero.mpr hs)))
      (pow_nonneg (show 0≤T*A by positivity) S.card)
    calc
      _ ≤ co S*(T*A)^S.card:=mul_le_of_le_one_left (mul_nonneg (cp S) (by positivity)) unit
      _ ≤ C^S.card*(T*A)^S.card:=z
      _ = ((C*T)*A)^S.card:=by simp only [mul_pow];ring
  · have mS:mass k S ≤ mass k univ:=by rw [stairK k (Finset.subset_univ S)];exact Nat.le_add_right ..
    have quiet:((levelsO (Y y) S).2 i r)=0:=(placedO _ (w.level' _) S).coverN i r (by dsimp [K] at rK;omega)
    have z:(tuftV f (levelsO (Y y) S)).2 i r=0:=by
      funext x;change f (((levelsO (Y y) S).2 i r) x)=0;rw [quiet];exact map_zero f
    rw [z];exact Fruit.zero.more (by positivity)

end YM.Integration.WilsonIndependentCollarSeedTariff
end
