import YM.AllOrder.High.Low
import YM.AllOrder.Burn.Officer
import YM.AllOrder.Burn.Notes
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    {H : Cash W s μ L Q o α T I} {J : Cash W s μ L Q o α T R} {p : BudgetPoint}
open YM.AllOrder.Burn
lemma mantle (R:ℕ→ℕ) (s : Molecule S) (k:ℕ) : prongs k S s ≤ prongsT R k S s:= by
 apply Finset.sum_le_sum; intro i hi
 rcases i with i|(i|(((i|i)|i))) -- third needs parenthesization i|(i|((i|i)|i))

 all_goals first | exact le_rfl| exact Nat.le_add_right ..
lemma tiredG (V:ℕ→ℕ) (i:H.fragrances)(h:tiredV H k i):tiredT H V k i:= by
 rcases h with h|h; swap; · exact Or.inr h
 exact Or.inl (le_trans h (Nat.add_le_add_right (Finset.sum_le_sum (fun _ _=>mantle ..)) (breadth H i)))
variable (χ:Chi)
def errorX (H:Cash W s μ L Q o α T I)(M:Set ℕ)(i:H.fragrances): Prop:= ∃ j:ℕ, j∉M∧ i=icon H j
abbrev burnoff (H:Cash W s μ L Q o α T I)(M:Set ℕ)(k:ℕ) (i:H.fragrances):Prop := tiredT H (typeT M k) (alt k) i ∨ errorX H M i
variable {M:Set ℕ}(k)
local notation "R'"=> typeT M k
local notation "b₀"=> alt k
lemma heirs (i:H.fragrances)(u:Option (Fin i.1))(j:ℕ)(hj:j∉M)(h:tiredT H (typeT M k) (alt k) i→False)(hp:Opacity.key S j∈ (i.2 u).val)(V:Config G c)(he:stream H χ V i≠0) : i=icon H j:= by
 have hc:= children χ i (fun z=>h (tiredG R' i z)) V he; have hv : qlocal74d_degreeT H R' b₀ i < b₀:= lt_of_not_ge (fun z=> h (Or.inl z)); apply Beam.lantern i (fun j=>Finset.card_pos.mpr ((hc.2.2 j).1.1)) _ u hp
 have h : 1+extraN k≤ cardT H R' b₀ i:= by
    apply le_trans (b:=prongsT R' b₀ S (i.2 u|>.val)); swap; · exact single_le_sum (f:=fun j=> prongsT R' b₀ S (i.2 j|>.val)) (fun _ _=>Nat.zero_le _) (mem_univ u)
    let z(x:Head S):=Sum.elim (fun _:Stores S=>0) (Silica.spikeT R' b₀) x; have hZ:z (Opacity.key S j)=1+extraN k:= congr_arg (1+·) (if_neg hj); rw [← hZ]; apply single_le_sum (f:=z) (fun _ _=>Nat.zero_le _) hp
 unfold qlocal74d_degreeT alt at *; omega
lemma bodies (i:H.fragrances) (h:¬ burnoff H M k i) (V:Config G c)(he:stream H χ V i≠0): i.1<alt k ∧ depth H i < Pressure.Stores.till s ∧ ∀ u,Ac.Spark H.supportP (i.2 u).val ∧ (i.2 u|>.val.card)≤alt k ∧∀ p∈(i.2 u|>.val),Beam.Pennies S p ∨ ∃ j∈M, Opacity.key S j=p:= by
 obtain ⟨v',hx⟩:=not_or.mp h; obtain ⟨hp,hB,hQ⟩:=children χ i (fun z=>v' (tiredG R' i z)) V he; refine ⟨hp,hB,fun u=> ⟨(hQ u).1,(hQ u).2.1,fun p h=>?_⟩⟩; rcases (hQ u).2.2 p h with h|⟨j,rfl⟩; exact Or.inl h; by_cases ht:j∈M; · exact Or.inr ⟨j,ht,rfl⟩
 exact (hx ⟨j,ht,heirs k χ i u j ht v' h V he⟩).elim
end YM.PhysicalNext.Repeat.Height
