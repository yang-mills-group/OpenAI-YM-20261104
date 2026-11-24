import YM.RG01Estimate.MarkedExpense
import YM.RG01Estimate.RepriceRaw

/-! Use re-purchased weights in E6's held-variable angular estimate. Re-use the actual
path-mask values and sigma/precision/W windows, buy a new `Utopia` at the same physical
parameters. Exponents & geometry reused, no switching input coupling/domain. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Reprice

open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Coat Raw Pulse Footprint Shell Poll Pond Matter
open Blaze Brush Scroll Vine Polar Frond Silica Clutch Flux
open SliceRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P)

def rays (c f : Side) (E : Set ℕ) (K w : ℝ) : LogIndex c f → ℝ :=
    Sum.elim (Inherit.weight c f E K w) (Sum.elim (fun _=> 1) (fun _=>w))
def weigh (c f : Side) (E : Set ℕ) (K w : ℝ) : Alphabet c f → ℝ :=
    Sum.elim (fun _=>1) (Sum.elim (rays c f E K w) (fun _=> w))
lemma rays_ge (E : Set ℕ) {K w : ℝ} (hk : 1≤K) (hw : 1≤w) (j : LogIndex c f) : 1≤ rays c f E K w j := by
  rcases j with j|j|j
  · exact Inherit.weight_ge E hk hw j
  · exact le_refl _
  exact hw
lemma ones (E : Set ℕ) {K w : ℝ} (hk : 1≤K) (hw : 1≤w) (j : Alphabet c f) : 1 ≤ weigh c f E K w j := by
  rcases j with j|j|j
  · exact le_refl _
  · exact rays_ge E hk hw j
  exact hw

-- optional supplies initially in pure-real fixed inputs
set_option maxHeartbeats 600000 in
lemma logs :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ D : Patch, D.Branches P.bind G → ∀ (u v w p:ℝ),
    -(1/2:ℝ)<p → p<0 → u+v<p → 0≤w →
    ∀ (X E K f g : ℝ→ℝ), Rate G L u X → Rate G L v E → Rate G L w K →
      (∀ᶠ x in atTop,1 ≤ E x) → (∀ᶠ x in atTop,1 ≤ K x) →
      Rate G L (-(1/2:ℝ)) f → (∀ᶠ x in atTop, 0 ≤ f x) → Rate G L (-(1/2:ℝ)) g →
    ∀ (χ : Chi) (i : ℕ) (W : ℝ) (o:Target.Order G W),
    ∃ B C : ℝ→ℝ, Rate G L 0 B ∧ (∀ x, 1 ≤ B x) ∧ Rate G L p C ∧ ∀ᶠ s in atTop,
      ∀ (n m:Side) (S : StepData n m) (T : Tube G S), Works P L s S T → S.patch=D → Stamp T →
        Tent P L s o.K o.eta o.gap o.ample o.indexPay T → ShellAccess S G s W o.K o.γ → ∀ (R:Rep G m), Intake P T s R →
        ∀ Y : Set ℕ, Inherit.Debits R Y (X s) →
          ∃ U H, Eager Q o s (B s) i (f s) (g s) (C s) χ T R U H ∧
            Sales (radiusB s) Q.relative Q.ε (roadway T R (radiusB s) Q.halo)
              (fun j=> rays n m Y (E s) (K s) j* H j) (exCharge T R) (C s) := by
  let a:= Q.relative
  have hv : 0≤a := by unfold a Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  obtain ⟨N,hN⟩:= Inherit.priors P Q.halo Q.usable hv Q.grants.1 Q.grants.2.1 Q.grants.2.2
  obtain ⟨M,hM⟩:= Clutch.hearth P Q.halo Q.usable Q.grants.1 Q.grants.2.1 Q.grants.2.2 hv
  refine ⟨max N M,fun L hL D hD u v w p h hl hu hm X E K f g hx he hk he' hk' hf hp hg χ i W o=>?_⟩
  obtain ⟨B,hB,hFb,hP⟩:= hN L ((le_max_left ..).trans hL) _ _ _ _ h hu _ _ _ _ _ hx he hk he' hk' hf hg χ i o.a
  obtain ⟨B',hB',hFb',hP'⟩:= hM L ((le_max_right ..).trans hL) i χ o.a p h _ _ hf hg
  obtain ⟨A,hA,hG⟩:= Clutch.waits P L D hD o.K o.γ W o.a χ i hf hp hg o.indexPay o.f (p-w) Q.relative Q.ε
    (by linarith only [hl,hm]) hv Q.halo (by have h:=Q.buys; omega)
  obtain ⟨C,U,b,hC,hU,hY,hQ⟩:= Clutch.flick P L D hD o.K o.γ W o.a χ i hf hp hg o.indexPay o.f Q.relative Q.ε hv Q.halo
    (by have h:=Q.buys; omega) Q.table_exists
  let V x := B x+B' x+(1+U x)
  have hBB (x:ℝ): B x+B' x ≤ V x := le_add_of_nonneg_right (add_nonneg zero_le_one (hY x))
  have hBX x:1≤V x:= by unfold V; linarith only [hFb x,hFb' x,hY x]
  obtain ⟨R,hR,H'⟩:= Brush.expands i
  have hT:Rate G L p (fun x=> betaF G x L^p + (C x + K x*A x)):=
    Rate.power.add ((hC.weaken h.le).add (by convert hk.mul hA using 1; ring))
  refine ⟨V, _, (hB.add hB').add ((Rate.const 1).add hU), hBX, (Rate.power (a:=p)).add (hT.mul_left R),?_⟩
  filter_upwards [hP,hP',he',hk',hG,hQ,hT.below hl 1 zero_lt_one] with x hΨ hb hx' hK hZ hA h c f S T H hS hF ht hA' R' hr J hJ
  obtain ⟨y,he,hQ⟩:=hZ _ _ S T hS H hA' ht
  obtain ⟨hX,hY'⟩:= hA _ _ S T hS H hF ht hA'
  obtain ⟨k₀,k,hκ,hk,hW⟩:= hb c f S T R' H.length_eq hr
  obtain ⟨a,hi,hA⟩:= hΨ c f S T R' H.length_eq hr J hJ
  let w := Sum.elim a (Sum.elim (fun _:Miniature c f=> b x) y)
  let r := rays c f J (E x) (K x)
  let s:= betaF G x L^p
  have hhx := hi.together (hX.together (Inherit.fee_times he (zero_le_one.trans hK)))
  have hh : Sales (radiusB x) Q.relative Q.ε (roadway T R' (radiusB x) Q.halo) (fun i=> r i*w i)
      (exCharge T R') (s+(C x+K x*A x)):= by
    convert hhx using 1
    · rfl
    · funext i; rcases i with i|i|i <;> simp only [r,rays,w, Sum.elim, one_mul]
    · rfl
  have he' := Inherit.fee_shift hh (rays_ge J hx' hK)
  have hz := mul_nonneg hR (budget_nonneg (hh.hit 0))
  let W i:=R*w i
  have hs : Sales (radiusB x) Q.relative Q.ε (roadway T R' (radiusB x) Q.halo) (fun i=>r i* W i) (exCharge T R')
       (s+(R*(s+(C x+K x*A x)))) := by
    have hS' (i): r i* W i=R*(r i*w i):=by unfold W; ring
    simp_rw [hS']; exact (Inherit.fee_times hh hR).raise (le_add_of_nonneg_left (budget_nonneg (hk.hit 0)))
  refine ⟨k,W,⟨hk.raise (le_add_of_nonneg_right hz),Inherit.fee_shift hs (rays_ge J hx' hK),?_⟩,hs⟩
  intro E _ _ _ F Z v u z q t hΖ he hχ hM H'V ht k
  let I:= Z.input (worldZ Z R'.beta t); let f' j:= twigs R' T Z.B Q.halo j
  have hF i:1≤f' i:= le_add_of_nonneg_right (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have htH j (v w:ℕ)(k:ℝ)(hm:k ≤ V x) (he : f' j=1+(v+(w:ℝ))) : k*(v+(w:ℝ)) ≤ V x*f' j :=
    mul_le_mul hm ((le_add_of_nonneg_left zero_le_one).trans_eq he.symm) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (zero_le_one.trans (hBX _))
  let Δ p:= V x*f' p
  have hB: radiusB x=Z.B := congr_arg _ hΖ.symm
  refine ⟨fun j=>?_,fun j=>?_⟩
  · apply H' E _ (w j) (Δ _) (fun h=> logMoment (vary Z (v h)) o.a R' Q.table (u h) I (z h) j) _
      ((he'.atom hv Q.usable.le j (exChart ..)).trans ((le_abs_self _).trans h))
    rcases j with j|j|j
    · have hk:= hA F Z E I v u q z t hΖ hχ H'V ht j; rw [hB] at hk
      exact hk.climb le_rfl (htH _ _ _ _ ((le_add_of_nonneg_right (hFb' _)).trans (hBB _)) rfl)
    · have hp:= hY' E F Z R' v u z q t hΖ hχ he hM H'V ht hr j
      apply hp.climb le_rfl
      unfold Δ f' twigs lengths; simp only [Sum.elim,exCharge,Nat.cast_zero,add_zero]
      exact mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_left
        (add_nonneg (hFb x) (hFb' x)))) (by positivity)
    exact (hQ E F Z R' v u z q t hΖ hχ he hM H'V ht hr j).climb le_rfl (one_le_mul_of_one_le_of_one_le (hBX _) (hF _))
  have hv:= (hW F Z E I v u q z t hΖ hχ H'V ht).2 j; rw [hB] at hv
  exact hv.climb le_rfl (htH _ _ _ _ ((le_add_of_nonneg_left (hFb _)).trans (hBB _)) rfl)

end YM.RG01Estimate.Reprice
