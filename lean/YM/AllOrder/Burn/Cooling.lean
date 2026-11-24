import YM.AllOrder.Burn.Press
import YM.AllOrder.High.Skirt
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
open Song Beam
local notation "Bp"=> Beam.dashboard H
lemma shallT (u:ℕ→ℕ) (i k:ℕ)(h:¬tiredT H u k (icon H i)): coverNumber (radiusB s) (H.unionP (Brim.head i))≤ radiusB s:= by
  have he : depth H (icon H i)<Pressure.Stores.till s := lt_of_not_ge (fun ht=> h (Or.inr (Or.inr ht)))
  have hv : depth H (icon H i)= H.shapeW (Brim.head i):= by simp [depth,icon,once]
  rw [hv] at he
  have hx: Ac.Spark H.supportP (Brim.head i):= by
    unfold Brim.head; refine ⟨singleton_nonempty _, fun i hi j hj=>?_⟩; rw [mem_singleton.mp hi,mem_singleton.mp hj]; exact .refl
  have hk:= ((shaped (H:=H) (Brim.head i) hx).trans he.le).trans (show (Pressure.Stores.till s:ℝ) ≤ radiusB s from by exact_mod_cast Nat.div_le_self ..)
  exact_mod_cast hk
variable (p : BudgetPoint) (χ:Chi)
local notation "B"=> radiusB s
set_option quotPrecheck false
local notation "X:" => (Match.staple (H:=H) («J»:=H) rfl rfl rfl)
local notation "T0"=> tiredT H (typeT M k) (alt k)
variable {M:Set ℕ} {D : JointLoad.Heir.Record}
local notation "T₀"=> tiredT H (typeT M k) (alt k)
lemma icon_budget {q' κ : Chi}{b' : ℝ}(hb:p.B=radiusB s)(hX:Brim.Homes M H D q' κ χ b' p a γ q) (ht:preExponent p≤a): Meadow.Budget p (Bp) (fun i=> if ¬T₀ i∧ errorX H M i then Song.sequence H (Match.staple (H:=H) («J»:=H) rfl rfl rfl) χ i else 0) (γ+q):= by
 obtain ⟨⟨u,hu,hω,hV⟩,v,hp,hc,hv⟩:=hX; let f i:=u i+v i; have hx i:0≤ f i:= add_nonneg (hω i) (hc i); let η:ℕ↪H.fragrances:= ⟨icon H, icon_inj _ ⟩; let F(i:H.fragrances):= if ¬T₀ i ∧ errorX H M i then Function.extend η f 0 i else 0; let Q i:= if ¬T₀ i∧ errorX H M i then Song.sequence H (Match.staple (H:=H) («J»:=H) rfl rfl rfl) χ i else 0;
 have hB(i:H.fragrances) : p.Regular (Beam.dashboard H i).support (Q i) ∧ p.supBounds (Beam.dashboard H i|>.site) (Beam.dashboard H i|>.support) (Q i) (F i):= by
    unfold Q F; split
    next ht=> obtain ⟨h,⟨j,hv',rfl⟩⟩:= ht; obtain ⟨hV, hδ⟩:= hu j hv'; obtain ⟨hF,hΩ⟩:= hv j hv'; have he:= shallT _ j (alt k) h; rw [concern H,← hb] at he -- orientation
              rw [show extend η f 0 (icon H j)=f j from η.injective.extend_apply .., impact, show Song.sequence H (Match.staple (H:=H) («J»:=H) rfl rfl rfl) χ (icon H j)= announced H D q' κ b' j -glyph H D q' κ χ b' j from (by unfold Song.sequence; rw [AllOrder.High.flip_noop]; ext1 U; change -1*_= _-(stream H χ U (icon H j)+ announced H D q' κ b' j U); ring)]; exact ⟨CouplingShape.reg_sub hV hF,CouplingShape.sup_sub hV hF hδ (hΩ he)⟩
    next he=> exact ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
 refine ⟨F,fun i=>?_,hB⟩
 apply Beam.wallet η
 · refine budget_mono (budget_plus (hV i) (hp i)) ?_ ?_
   · intro j; split; exact mul_nonneg (hB _|>.2.1) (Real.exp_pos _).le; rfl
   intro j; change (if (Beam.dashboard H (icon H j)|>.site) = _ then _ else _)≤_; simp only [η,Function.Embedding.coeFn_mk, impact]; split;
   next h=>
     refine (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (hB (icon H j)|>.2.1)).trans ?_; rw [show _ + _ = _ from (Eq.symm (add_mul (u j) (v j) (Real.exp (a*(coverNumber p.B (plate H j|>.support))))))]; unfold F; split
     next hm=> rw [show Function.extend η f 0 (icon H j)=f j from η.injective.extend_apply ..]
     next hx'=> rw [zero_mul]; exact mul_nonneg (hx j) (Real.exp_pos _).le
   next => simp
 intro b hb; dsimp only; unfold F; split_ifs
 next hi hv=> exact False.elim (hb (by obtain ⟨w,-,h⟩:=hv.2; exact ⟨w,h.symm⟩))
 next hi hv=>rw [zero_mul]
 next hv=> rfl
end YM.PhysicalNext.Repeat.Height
