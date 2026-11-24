import YM.AllOrder.Burn.Cooling
import YM.QuadraticLocal.Vacuum.Cloud
/-!
# Recovering the arbitrary input factor before summing at *each* root

On the same carriers as the ALL-ORDER unmarked lift, paying *either* the full path
height, OR one old E weight AND height three. The latter is possible even with ONE
tagged regular E if it doesn't stand strictly alone. If it does, there's a separate
old-E-only contraction proof -- see `Brim.selectiveP`. No speculative cancellation with the
low (transported and realigned) model is involved. No large-torus payment.

Extension of `AllOrder/Burn/Revenue.lean`. Variants of `le_productW` etc. also occur
in `CoreSixteen/Vacuum` and `Local1020/Inherit` with other remainder
conventions; not assumed established here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
    {χ : Chi} {H : Cash W s μ L Q o α T R}
local notation "D"=> grow G L s
section collective
variable (H)
def wideProduct (τ:Multiplier)(π:ℕ) (z:H.fragrances) : ℝ:= ∏ i, cloudW τ D π S (z.2 i).val
-- the factor earned on the whole connected term
abbrev omensW (τ:Multiplier)(π:ℕ)(z:H.fragrances) :ℝ:=
  wideProduct H τ π z * D ^ breadth H z * Real.exp (Q.mark L μ s*overlap H z)* Real.exp (Q.ε*depth H z)
variable {H}
set_option maxHeartbeats 600000 in
lemma clouds_one (D':ℝ)(S':StepData c f) (τ:Multiplier)(π:ℕ)(h:1≤D')(p:Molecule S'):1≤ cloudW τ D' π S' p:= Finset.one_le_prod (fun i _=> headW_up _ _ _ _ h i)
lemma wideOne (τ:Multiplier)(π:ℕ)(h:1≤D)(z:H.fragrances): 1≤ wideProduct H τ π z:= Finset.one_le_prod fun i _=> clouds_one (grow G L s) S τ π h _
set_option maxHeartbeats 600000 in
lemma breadthWeight (τ:Multiplier)(π:ℕ)(h:1≤D) (z:H.fragrances): wideProduct H τ π z * D^breadth H z ≤ omensW H τ π z:= by
 have hPos:1 ≤ Real.exp (Q.ε*depth H z) := Real.one_le_exp (mul_nonneg Q.usable.le
        (sum_nonneg fun i _=> H.positive_volume _))
 have ht:0 ≤ grow G L s:=zero_le_one.trans h
 have hM:1≤Real.exp (Q.mark L μ s*overlap H z):=Real.one_le_exp (mul_nonneg (H.laws.acquired.marked) (Nat.cast_nonneg _))
 have hy:= zero_le_one.trans (wideOne τ π h z)
 exact (le_mul_of_one_le_right (by positivity) hM).trans (le_mul_of_one_le_right (by positivity) hPos)
variable (N : Captain H j C' d v Y A b r B q k χ) (hd : 1 ≤ grow G L s) {π:ℕ} {τ:Multiplier} (hh : Lions τ π N.conduit)
set_option maxHeartbeats 600000 in
lemma wieldW (z:H.fragrances):clusters H.seam (fun u:H.ThinP=> crestW τ π H u.val*N.stone u) z.2 =
     omensW H τ π z * N.design z := by
  unfold Captain.design clusters crestW gust
  unfold omensW wideProduct breadth depth overlap
  simp only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Nat.cast_sum,mul_sum,Real.exp_sum]; ring
variable (n : ℕ) (ht : Armada Q L μ a s i B j k)
include N ht hd hh
lemma masterHit
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2) (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=>omensW H τ π z*N.markΦ z n) a
        (collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹)) := by
 intro x
 let D':=grow G L s
 have hD:0<D':=zero_lt_one.trans_le hd
 have hδ:= ht.delta; have he:0 ≤ shiftG s:= by unfold shiftG; positivity
 have hb:0≤collars G i s j n:= by unfold collars Reserves.polyPrice; positivity
 let v:=collars G i s j n
 have hu:= log_hit_tail _ _ _ H.testS (markerW N hd hh i a ht.delta ht.little ht.earned hs hp) (add_nonneg ht.gain ht.delta.le) 0 x
 simp only [pow_zero,mul_one] at hu
 have hy:= budget_scale hb hu
 have hq (z:H.fragrances):0 ≤ omensW H τ π z:= by
     apply le_trans _ (breadthWeight τ π hd z); exact mul_nonneg (zero_le_one.trans (wideOne τ π hd z)) (pow_nonneg hD.le _)
 refine budget_mono hy (fun z=> ?_) fun z=> ?_
 · dsimp only; split
   next => exact mul_nonneg (mul_nonneg (hq z) (mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _))) (Real.exp_pos _).le
   exact le_rfl
 dsimp only; split
 next hx=>
   rw [if_pos (show 0≤z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,hx⟩),wieldW (τ:=τ) (π:=π) N z]
   let p:ℝ:=coverNumber (radiusB s) (reachability (H:=H) z); have hg:0≤p:=Nat.cast_nonneg _
   change omensW H τ π z * ((shiftG s*(1+p))^(n*j)*N.design z) *Real.exp (a*p) ≤ v*(omensW H τ π z*N.design z*Real.exp ((a+i)*p))
   rw [mul_pow]; refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
         (polynomial_cost ht.delta hg _) (pow_nonneg he _)) (N.pvc _)) (hq z)) (Real.exp_pos _).le).trans_eq ?_
   unfold v collars Reserves.polyPrice; rw [add_mul a i p, Real.exp_add]; ring
 exact hy.1 z
omit hh N ht hd
end collective
section restores
open YM.AllOrder.Burn
variable (τ:Multiplier) (π:ℕ)
variable (hd:1 ≤ grow G L s) {M:Set ℕ}
local notation "T0"=> tiredT H (typeT M ℓ) (alt ℓ)
-- no error on a Head: compare to the analytic ruler
set_option maxHeartbeats 600000 in
lemma clearHeadW (M:Set ℕ)(j:ℕ)(d:ℝ)(hd:1≤d)(z:Head S)
    (h:∀ i, z=Opacity.key S i→ i∈M):
    d^(Sum.elim (fun _:Stores S=>0) (Silica.spikeT (typeT M j) π) z) ≤ HeadW τ d π S z:= by
  rcases z with z|p|(z|z|z)|z
  · exact (pow_zero d).le
  · exact (pow_zero d).le
  · rcases z with i|z
    · have hx := h i rfl
      change d^ (1+typeT M j i) ≤ d^1 * τ.weight i; unfold typeT; rw [if_pos hx,add_zero]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hd) _) (τ.upkeep _)
    change d^(gradeA π c f (Sum.inr z)+0)≤ d^gradeA π c f (Sum.inr z)*1
    rw [add_zero,mul_one]
  · exact (pow_zero d).le
  · exact le_rfl
  · exact le_rfl
set_option maxHeartbeats 600000 in
lemma hasHeads (M:Set ℕ) (k:ℕ) (d:ℝ) (hd:1≤d)(a:Molecule S) (h:∀ l,l∉M→ Opacity.key S l ∉ a) : d^(prongsT (typeT M k) π S a) ≤ cloudW τ d π S a:= by
 unfold prongsT cloudW; simp only [← Finset.prod_pow_eq_pow_sum]
 gcongr with i hi
 apply clearHeadW τ π M k d hd
 rintro j rfl
 exact Classical.byContradiction (fun h₁=> h j h₁ hi)
private lemma prod_le_X {ι:Type*} [Fintype ι](d:ℝ) (w:ι→ℕ)(z:ι→ℝ)(hd:1≤d)(h:∀ i,d^(w i)≤z i):d^(∑ i,w i)≤ ∏ i,z i:= by
 rw [← Finset.prod_pow_eq_pow_sum]; exact Finset.prod_le_prod (fun i _=>pow_nonneg (zero_le_one.trans hd) _) (fun i _=>h i)
include hd
set_option maxHeartbeats 600000 in
lemma clearEarnW (M:Set ℕ)(j:ℕ)(z:H.fragrances)
    (h:∀ i x, x∉M → Opacity.key S x∉(z.2 i).val): D^(cardT H (typeT M j) π z) ≤ wideProduct H τ π z:= by
 exact prod_le_X (grow G L s) (fun i:Option (Fin z.fst)=>prongsT (typeT M j) π S (z.2 i).val) (fun i=>cloudW τ _ π S (z.2 i).val) hd (fun i=>hasHeads τ π M j _ hd _ (h i))
omit hd
set_option maxHeartbeats 600000 in
lemma le_productW {ι:Type*} (p:ℝ) (s:Finset ι) {w:ι→ℝ} (hw:∀ i, 1≤w i)(i:ι)(hi:i∈s)(h:p ≤ w i): p ≤ ∏ i∈s,w i :=
  h.trans ((le_mul_of_one_le_right (zero_le_one.trans (hw i)) (Finset.one_le_prod (f:=w) (s:=s.erase i) (fun _ _=> hw _))).trans (by rw [Finset.mul_prod_erase _ w hi]))
lemma ageIcon (M:Set ℕ)(j:ℕ)(i:ℕ)(h:i∉M):
    qlocal74d_degreeT H (typeT M j) π (icon H i) = 1 + extraN j+1:= by
  simp [qlocal74d_degreeT, icon,once,cardT,breadth, Brim.head, prongsT,Silica.spikeT, Silica.Clutch.heightT,Raw.gradeT, Raw.gradeA,Raw.stake,typeT,Opacity.key,h]
set_option quotPrecheck false

set_option maxHeartbeats 400000 in
lemma many_when (l:ℕ)(hL:l∉M)(z:H.fragrances)(i:Option (Fin z.1))(hx:Opacity.key S l∈ (z.2 i).val)(h : alt ℓ ≤ qlocal74d_degreeT H (typeT M ℓ) (alt ℓ) z):¬ breadth H z ≤ 1:= by
      intro he; have hu (u:Option (Fin z.fst)) : 1≤ (z.2 u).val.card:= by
          refine Nat.succ_le_of_lt (Finset.card_pos.mpr ?_)
          obtain ⟨x, hx⟩:= ((z.2 u).property).1; change x ∈ Finset.biUnion (z.2 u).val H.supportP at hx; obtain ⟨k,hk,-⟩:= mem_biUnion.mp hx; exact ⟨k,hk⟩
      rw [Beam.lantern z hu he i hx,ageIcon (H:=H) (alt ℓ) M ℓ l hL] at h; simp only [alt] at h; omega
private lemma recovers_math (d w p:ℝ)(hd:1≤d)(b:ℕ) (h:¬ b≤1)(hp:d*w≤p)(ht:1≤p):d^3*w ≤ p*(d^b):= by
 rw [show d^3*w = d*w*(d^2) by ring]; exact mul_le_mul hp (pow_le_pow_right₀ hd (by omega)) (pow_nonneg (zero_le_one.trans hd) _) (zero_le_one.trans ht)
private lemma le_Here (d:ℝ)(hd:1≤d)(p:Molecule S)(i:ℕ)(h:Opacity.key S i∈p): d * τ.weight i ≤ cloudW τ d π S p:= by
 have he : HeadW τ d π S (Opacity.key S i)= d * τ.weight i:= by change d^1 * _=d* _; rw [pow_one]; rfl
 exact le_productW _ _ (headW_up τ d π S hd) (Opacity.key S i) h (le_of_eq he.symm)

include hd
lemma receivesW (z:H.fragrances)(i:Option (Fin z.1))(j:ℕ)(h:Opacity.key S j∈(z.2 i).val):
 D*(τ.weight j)≤wideProduct H τ π z:= by
 exact le_productW (w:=fun i:Option (Fin z.1)=>cloudW τ (grow G L s) π S (z.2 i).val) _ _ (fun i=> clouds_one _ S τ π hd (z.2 i).val) i (mem_univ i) (le_Here τ π _ hd _ j h)
set_option maxHeartbeats 400000 in
lemma touchesW_age (w:ℝ)(l:ℕ)(z:H.fragrances) (i:Option (Fin z.fst))(hx:Opacity.key S l∈ (z.2 i).val)(hy:w≤τ.weight l)(hh:¬ breadth H z ≤ 1): D^3*w ≤ wideProduct H τ (alt ℓ) z * D^breadth H z:=by
    have he:D*w ≤D*τ.weight l:=mul_le_mul_of_nonneg_left hy (zero_le_one.trans hd)
    exact recovers_math (grow G L s) w _ hd (breadth H z) hh (he.trans (receivesW τ (alt ℓ) hd z i l hx)) (wideOne _ _ hd z)
set_option maxHeartbeats 600000 in
lemma earnsW_low (w:ℝ) (hw:1≤w)(hy:∀ i, i∉M→ w≤τ.weight i)
    (z:H.fragrances) (h:T0 z)
    (hc : D^alt ℓ ≤ Real.exp (Q.mark L μ s)) (hx : D^alt ℓ≤Real.exp (Q.ε*Pressure.Stores.till s)) : D^alt ℓ ≤ omensW H τ (alt ℓ) z ∨ D^3*w ≤ omensW H τ (alt ℓ) z := by
  have hPos:1 ≤ Real.exp (Q.ε*depth H z) := Real.one_le_exp (mul_nonneg Q.usable.le
        (sum_nonneg fun i _=> H.positive_volume _)); let D':= D; let π':=alt ℓ
  have hg:= zero_le_one.trans hd
  have ht':0≤Q.mark L μ s:= H.laws.acquired.marked
  have hf:= one_le_mul_of_one_le_of_one_le (wideOne τ (alt ℓ) hd z) (one_le_pow₀ (n:=breadth H z) hd) -- check
  have hM:1≤Real.exp (Q.mark L μ s*overlap H z):=Real.one_le_exp (mul_nonneg ht' (Nat.cast_nonneg _))
  rcases h with h|h|h
  · by_cases hy':∃ i l, l∉M ∧ Opacity.key S l∈(z.2 i).val
    swap; · left; have hh:=clearEarnW τ π' hd M ℓ z (by push Not at hy'; exact hy'); refine (pow_le_pow_right₀ hd h).trans ((le_trans ?_ (breadthWeight τ (alt ℓ) hd z))); unfold qlocal74d_degreeT; rw [pow_add]; exact mul_le_mul_of_nonneg_right hh (pow_nonneg hg _)
    right; obtain ⟨i, l, hL, hx⟩:= hy'
    exact (touchesW_age τ hd w l z i hx (hy _ hL) (many_when l hL z i hx h)).trans (breadthWeight τ _ hd z)
  · exact Or.inl (hc.trans ((Real.exp_monotone (le_mul_of_one_le_right ht' (show (1:ℝ)≤ overlap H z by exact_mod_cast h))).trans ((le_mul_of_one_le_left (Real.exp_pos _).le hf).trans (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hf) (Real.exp_pos _).le) hPos))))
  exact Or.inl (hx.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_mul_of_one_le_of_one_le hf hM))))
end restores
end YM.PhysicalNext.Repeat.Height
