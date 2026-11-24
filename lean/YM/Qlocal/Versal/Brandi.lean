import YM.Qlocal.Versal.Verses
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Versal
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar Progress.DirectedRecipe RGComparison01 AllOrder AllOrder.Burn AllOrder.Till
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge} {c f C F: Side} {W₀:Burn.Locale G} {R:RG.Rep G f} {R':RG.Rep G F}
    {p p' : ℝ} {n b ℓ r k:ℕ}
-- ℓ capacity, one labelled copy per site, for either analytic ζ or further spends.
variable {X:Burn.Seed R W₀}
namespace Pad
variable (Z:Pad X k)
section cons
-- Extend any pure auxiliary Rep. Does not depend on period limits.Real Peelaʷ.B
variable (U:Burn.Seed R W₀)(h:r≤k)(ht:R.activities.Valid R.p p p')(P:r≤R.p.B)
structure Localizes (R R':RG.Rep G f):Prop where
  evap : R'.eval=R.eval
  stands : R'.path = R.path
  funded : R'.p=R.p
  currency: R'.beta=R.beta
  plane : R'.clip=R.clip
  gas : R'.activities.K=R.activities.K
  wrap : R'.activities.forced=R.activities.forced
-- charges same scalar too!
lemma term : Nonempty (Pad U 0):= by
 let f: Site f × Fin 0→ ℕ:= fun i=>Fin.elim0 i.2; exact ⟨⟨⟨f,fun i _ _=> Fin.elim0 i.2⟩, fun i=>Fin.elim0 i.2,fun i=>Fin.elim0 i.2,fun i=>Fin.elim0 i.2⟩⟩
include U ht
lemma extension (hq:faded U) (k:ℕ): ∃ (R': RG.Rep G f)(u:Burn.Seed R' W₀),Localizes R R' ∧ faded u ∧ Nonempty (Pad u k) ∧ R'.activities.Valid R'.p p p':= by
 induction k with
 | zero=> exact ⟨R,U,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,hq,term U,ht⟩
 | succ k ih=> obtain ⟨T,V,hT,hr,⟨v⟩,hv⟩:= ih; exact ⟨Burn.rise T (zeroB G), night V,⟨(funext (lately hv)).trans hT.evap,hT.stands,hT.funded,hT.currency,hT.plane,hT.gas,hT.wrap⟩,serene V hr, financed V v, honest hv⟩
end cons
section marks
open PhysicalNext.Repeat.Lotus Merge.Palette Ovens
-- compile.You.Tert. Charge.V Reach symmetric.Pay.Prime.Kernel.Writing.
local notation "T₀"=>R.p
local notation "A"=>R.activities
structure Herb (p:BudgetPoint)(x:Site f)(V:Config G f→ℝ)(d:ℝ):Prop where
    regular : p.Regular (court x p.B) V
    funded : p.supBounds x (court x p.B) V d
variable {i: Names f k} (m:ℕ)(z:Site f)(V:Config G f→ℝ)(Q:Herb R.p i.1 V p)
lemma stipend {p:BudgetPoint}{x:Site f} {y:Config G f}(hy:Healthy p.threshold (court x p.B) y) (h:Herb p x V p'): ‖V y‖≤p' := h.funded.2 y hy [] (Nat.zero_le p.order) (by simp)
include Z Q
set_option quotPrecheck false
local notation "P"=> court i.1 R.p.B
set_option quotPrecheck false
noncomputable def bark : Leaf R where
    turn := Wing.logKey (Z.slip i)
    ingredient := masked R.p.threshold (court i.1 R.p.B) V
    scopedR := by change UsesFinal _ ((A).reg (Z.slip i)).support _; rw [Z.ready]; intro x y hl hx; let T:=R.p.threshold; have he:Healthy T P x ↔ Healthy T P y:= by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty, show P∩flags T x=P∩flags T y from hx]
                  by_cases hh: Healthy R.p.threshold (court i.1 R.p.B) y
                  · exact (masked_eq _ _ _ _ (he.mpr hh)).trans ((Q.regular.sites _ _ hl).trans (masked_eq _ _ _ _ hh).symm)

                  exact (masked_ne _ _ _ _ (mt he.mp hh)).trans (masked_ne _ _ _ _ hh).symm
    grant U h := by by_contra hx; apply h; apply masked_ne; change ¬ Healthy R.p.threshold (R.activities.reg (Z.slip i)).support U at hx; rw [Z.ready] at hx; exact hx
    blank := Z.quiet i
    weight := p
    earn U:= by by_cases h:Healthy R.p.threshold (court i.1 R.p.B) U; · rw [masked_eq _ _ _ _ h]; exact stipend _ h Q
                rw [masked_ne _ _ _ _ h,norm_zero]; exact Q.funded.1
    glows := by intro x U; by_cases h:Healthy R.p.threshold P U; · rw [masked_eq _ _ _ _ h,masked_eq, Q.regular.symmetry]; unfold Healthy; rw [gauge_flags]; exact h
                rw [masked_ne _ _ _ _ h, masked_ne]; unfold Healthy; rw [gauge_flags]; exact h -- case indent
    borel:= masked_measurable _ _ _ Q.regular.borel -- arity
-- Lens_L transport any.Auth discovered.Mask only.
end marks
end Pad
end YM.Qlocal.Versal
