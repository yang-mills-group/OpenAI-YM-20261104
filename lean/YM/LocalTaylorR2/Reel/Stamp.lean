import YM.LocalTaylorR2.Reel.Thicket
/-! # Charge selection exactly on Beam.lit. Includes every E-degree partner. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Brim
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
open YM.RG01.Survive Port Candle
-- patrimonial faith coherence. lit is NOT a count of perturbative insertions. only a guarantee of affordable norms
open YM.RG01.Survive Port Candle Opacity
variable (X:Alliance I H 1 0)(hk:X.units=Equiv.refl _)
lemma spot (hp:R.path=R'.path)(hr:R'.activities.reg=R.activities.reg)(hK:R'.activities.forced=R.activities.forced)
    (ha:X.units=Equiv.refl _)(i:I.fragrances) : Beam.lit I i ↔ Beam.lit H (X.furrow i):= by
   refine or_congr (stilled X (hp:=hp.symm) (hα:=hr) (hA:=hK) ha i) ⟨?_,?_⟩
   · rintro ⟨k,rfl⟩; exact ⟨k,(Beam.mimics I X ha k).symm⟩
   rintro ⟨k,hk⟩; exact ⟨k,X.furrow.injective ((Beam.mimics I X ha k).trans hk)⟩
lemma afforded (z:H.fragrances) (he : ∀ i,1 ≤ (z.2 i).val.card) (i:Option (Fin z.fst)) (j:ℕ) (hs: key S j∈ (z.2 i).val): Beam.lit H z:= by
   by_contra hh; obtain ⟨hh,hv⟩:= not_or.mp hh
   have hn:= (not_or.mp hh).1; unfold degree at hn
   have hL:1 ≤ acme H z:=by
     apply le_trans _ (single_le_sum (f:=fun i=> pins S (z.2 i).val) (fun _ _=>Nat.zero_le _) (mem_univ i))
     exact single_le_sum (f:=Sum.elim (fun _: Stores S=>0) Silica.horn) (fun _ _=>Nat.zero_le _) hs
   exact hv ⟨_,(Beam.lantern z he (by omega) i hs).symm⟩

variable (E D:Reel.Scroll G f)
lemma alone (i:LogIndex c f)(h : ∀ j:ℕ,key S j≠ identityLog (S:=S) i): sprout H E i=sprout H D i:= by
  rcases i with i|i|i
  · rcases i with i|i|i|i|i; · exact (h i rfl).elim
    all_goals rfl
  · rcases i with i|i|i <;> rfl
  rcases i with i|i|i|i|i <;> rfl
lemma existsH (p:H.ThinP)(k:Orders n)(he:∀ j:ℕ,key S j∉p.val): team H E (χ:=χ) p k=team H D (χ:=χ) p k:= by
   unfold team; ext V; split; swap; · rfl
   next h=>
     have h i : sprout H E (i:↥(logs p.val)).val=sprout H D i.val:= by
        apply alone; intro j h; apply he j; rw [h]; exact (log_occ _).1 i.2
     unfold press; simp_rw [h]
lemma short (p:H.ThinP)(i:Orders n)(he:¬live H p): team H E (χ:=χ) p i=fun _=>0:= by ext U; exact if_neg he
lemma hug (i:H.fragrances) (hn:¬ Beam.lit H i) (F:ℕ→ Prop): fullSegments (fun _ k=> F k) (team H E (l:=n) (χ:=χ)) i=fullSegments (fun _ k=> F k) (team H D (l:=n) (χ:=χ)) i:= by
   ext V
   unfold fullSegments; apply congr_arg; apply sum_congr rfl; intro q hq
   unfold aliquot; by_cases he:∀ j,live H (i.2 j)
   · have hc j :1 ≤ (i.2 j).val.card:= Finset.card_pos.mpr (he j).1.1.1
     apply prod_congr rfl; intro j _; rw [existsH H E D _ _ (fun z hz=> hn (afforded H i hc j z hz))]
   push Not at he; obtain ⟨j,hj⟩:=he
   have hv E:team H E (χ:=χ) (i.2 j) (q j) V=0:=if_neg hj
   exact (prod_eq_zero (Finset.mem_univ j) (hv _)).trans (prod_eq_zero (Finset.mem_univ j) (hv _)).symm

lemma emitsEqual (hp:R.path=R'.path)(hr:R'.activities.reg=R.activities.reg)(hK:R'.activities.forced=R.activities.forced)(ha:X.units=Equiv.refl _)
   (χ:Chi)(γ:ℝ)(p:ℕ)(φ:Bool)(F:ℕ→Prop)(q:ℕ)(hq:¬ Height.chosen I (Beam.lit I) (pennant I q).2): sight H E X χ γ p φ F q=sight H D X χ γ p φ F q:= by
   have he (i:Magazine I) (hh:¬ Height.chosen I (Beam.lit I) i): Reel.crawl H E X χ γ p φ F i=Reel.crawl H D X χ γ p φ F i:= by
      unfold crawl; rcases i with i|i <;> dsimp only [Sum.elim]
      apply congr_arg; apply hug; exact fun h=> hh ((spot H X hp hr hK ha i).2 h)
   apply congr_arg (fun f=>Rim c • (fun U=> f ((pennant I q).1.view U))) (he (pennant I q).2 hq)
end YM.LocalTaylorR2.Reel
