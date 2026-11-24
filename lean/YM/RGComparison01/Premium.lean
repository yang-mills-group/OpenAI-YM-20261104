import YM.RGComparison01.Harbour
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Horns

/-! # Hard-factor payments. Consuming actual exponential reserves.

 Keep warning/envelope split on Gaussian, extended tail orders. Other
 than weight account, same payment as in `twinkles`. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Q : YM.ConnectedActivityE6.Target G P}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G} {o : Target.Order G W} {χ : Chi}

open PhysicalNext.Repeat.Height
def crestP (c f : Side) (V : ℕ → ℝ) (t : ℝ) : Alphabet c f → ℝ :=
    Sum.elim (fun _=>1) (Sum.elim (leafletP c f V t) fun _=>t)
lemma crestP_ge (V : ℕ→ℝ) (t : ℝ) (h : 1 ≤ t) (hv : ∀ i,1 ≤ V i) (i : Alphabet c f) :
    1 ≤ crestP c f V t i := by
  rcases i with i|i|i
  · exact le_rfl
  · exact leafletP_ge h hv i
  exact h

def Worthy {C : ℝ} {H : Cash W s μ L Q o C T R} {χ : Chi} (I : Utopia H j v d r C' χ) (V : ℕ→ℝ) (t : ℝ) :=
    Sales (radiusB s) Q.relative Q.ε (footprints T R Q.halo (radiusB s))
      (fun i=> (crestP c f V t i * grow G L s ^ horn i) * I.flair i)
      (Sum.elim (Raw.forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L s)
namespace Utopia
lemma abundant (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0 < W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W) (v w : ℝ→ℝ) (κ : ℕ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤v x) → Rate G L (-(1/2)) w → ∃ (C':ℝ) (r:ℝ→ℝ), 0≤C' ∧ Rate G L 0 r ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T → ∀ (R:Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),
      ∀ Z : ℕ → ℝ, RGComparison01.Tithe.Ticket R.activities R.p Z (2 * incomingE G L x) →
      ∃ Ξ : Utopia H i (v x) (w x) (r x) C' χ, Worthy Ξ Z (grow G L x^κ) := by
  obtain ⟨t,hT,ht⟩:= exists_between Q.start
  obtain ⟨n,hn⟩:= Clutch.Market.longPrices P Q hT (ht.trans Q.stop)
  refine ⟨n,fun L hL D hd i χ W hw μ hm o v w κ hv hwV hW=>?_⟩
  obtain ⟨C,hC,hΨ⟩:= Clutch.chimney P D L hd o.K o.γ W o.a χ i Q.table_exists hv hwV hW μ o.indexPay o.f o.large hw o.gamma
  obtain ⟨B,J,hB,hJ,hv',h⟩:= hn L hL D hd i χ W o v w κ hv hwV hW
  obtain ⟨A,hA,hy,hQ⟩:=Clutch.ash G L χ i hW hv W o.a Q.halo (by have h:=Q.buys; omega)
  obtain ⟨t',ht'⟩ := exists_lt (t-((3/8:ℝ)*κ+(3/8:ℝ)*(2:ℕ)))
  let g x:= betaF G x L ^ t'; let Z x:= B x+A x; have hZ x:1≤Z x:= (hv' x).trans (le_add_of_nonneg_right (hy x))
  have hp:0≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  let u := Coat.topStorm D+1; have hu : 0 ≤ u := by unfold u; linarith [topStorm_one D]
  have he : Rate G L (3/8) (grow G L) := Rate.power
  let Saks x := grow G L x^κ*grow G L x^2
  have hf : Rate G L t (fun x=> Saks x*g x) := ((((he.pow κ).mul (he.pow 2)).mul (Rate.power (a:=t'))).weaken (by linarith only [ht']))
  obtain ⟨Y,hY,hF⟩:= Coat.alarm_bills (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) P L (t'*2-1) (half_pos o.rare)
  obtain ⟨b,hb,hH⟩:= exponent_fee G L Q.halo Q.relative Q.ε t u hp (fun x=> Saks x*g x) hf
  refine ⟨C,Z,hC,hB.add hA,?_⟩
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hΨ,h,hQ,hF,hY (t'*2) (by linarith),Q.pay_for L hm hC,(hJ.add (hJ.add hb)) Q.rate ht]
    with x hgθ hΨ h hQ he hV hA hv c f S T hS hF R C' H Ω hΩ
  have hΓ:= H.laws.data; have hh:= H.laws.intake
  have hΘ: 0<betaF G x L:=by have he:=hh.height; rw [hΓ.funds.length_eq] at he; linarith
  have hg:0≤g x:= by unfold g; positivity
  have h' := (hΓ.localP)
  obtain ⟨V,y,hG,H'⟩:= h _ _ S T hΓ.funds hS hF h' hΓ.access R hh Ω hΩ
  have hΞ:=hH x c f S hΓ.funds.length_eq (by have h:= hΓ.room.sight; omega) (mul_nonneg hu (mul_nonneg (mul_nonneg (pow_nonneg (show 0≤grow G L x from Real.rpow_nonneg (zero_le_one.trans hgθ) _) _) (pow_nonneg (show 0≤grow G L x from Real.rpow_nonneg (zero_le_one.trans hgθ) _) _)) hg))
  have hl : Sales (radiusB x) Q.relative Q.ε (footprints T R Q.halo (radiusB x)) (fun i=> (crestP c f Ω (grow G L x^κ) i *grow G L x^horn i)*rates V y (u*g x) i) (Sum.elim
    (Raw.forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L x) := by
    have ht:= (H'.first.together (hG.together hΞ)).raise ((le_abs_self _).trans hv)
    convert ht using 1
    · rfl
    · funext i; rcases i with i|i|i <;> simp only [Sum.elim,rates,horn,crestP,tallyP]; simp
      unfold Saks; ring
    · rfl
  have h₀ : 1 ≤ grow G L x := Real.one_le_rpow hgθ (by norm_num)
  refine ⟨⟨V,y,u,hu,g x,hg,hF,hZ x,(by rw [hΓ.funds.length_eq]; exact hA R.beta (hΓ.funds.length_eq ▸ hh.window.1)),
      Market.salesM _ (fun i => one_le_mul_of_one_le_of_one_le (crestP_ge _ _ (one_le_pow₀ h₀) hΩ.1 i) (one_le_pow₀ h₀)) hl,?_,?_⟩,hl⟩
  · intro E _ _ _ F X A' v' w' z q ht hX hχ hZ' hM hp F' k p hv
    have ht' := h' F X ht hX hZ'

    obtain ⟨hL,hK⟩:=H'.stamina E F X A' v' w' z q ht hX hχ hZ' hM hp k
    rcases p with p|p
    · by_cases he: Packets.connected S Q.halo X.B p
      swap; · apply Brush.zi (Eventually.of_forall (fun y:E=> if_neg he)) (by unfold stout Mixed.costs; simp only [Sum.elim,if_neg he]; exact le_rfl)
                (show 0≤Z x*1 from mul_nonneg (zero_le_one.trans (hZ x)) zero_le_one)
      have hh' : Healthy (Pressure.temp X.x) (p.dome (Q.halo*X.B)) X.V := by unfold Coat.B; rw [ht] at *; exact hv
      have hX:= hΨ c f S T hS hΓ.funds hΓ.access hΓ.grant E z A' F X R v' q w' ht hχ hX ht' hM hh hp p Q.halo k Q.buys
        (Packets.shares_nonzero S _ _ he) hh'
      apply hX.shimmy (Eventually.of_forall (fun y=> if_pos he))|>.climb _ (show 1≤Z x*1 by rw [mul_one]; exact hZ _)
      unfold stout; simp only [Mixed.costs,Sum.elim,if_pos he,steamP,Target.costs,Buy.quote]; unfold Grant.credit Coat.t; rw [ht,hΓ.funds.length_eq]
    have ha : 0 ≤ twigs R T X.B Q.halo p := add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hv : B x*twigs R T X.B Q.halo p≤Z x*twigs R T X.B Q.halo p := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hy x)) ha
    rcases p with p|p|p
    · exact (hK p).climb le_rfl hv
    · exact (hL p).climb le_rfl hv
    unfold u; rw [← hS]; refine (hQ c f S T F X R ht hχ hΓ.funds.length_eq
      (show 0<W*X.t from mul_pos hw ht'.sails.room.fiery) _ q z A' v' w' hp hM p k _).climb le_rfl ?_
    apply le_trans _ (mul_le_mul_of_nonneg_right (show A x ≤ Z x from le_add_of_nonneg_left (zero_le_one.trans (hv' _))) ha)
    apply le_of_eq; unfold twigs lengths; simp
    exact Or.inl rfl
  intro F X ht hK _ hp K
  have hV' : betaF G x L^(t'*2)=g x^2 := by unfold g; rw [Real.rpow_mul hΘ.le, Real.rpow_two]
  exact (he.2 c f S T F X ht hΓ.funds.length_eq (h' F X ht hK hp).sails R (ht.symm ▸ hh) K).trans
    (pow_le_pow_left₀ he.1 (((le_abs_self _).trans hV).trans_eq hV') _)
end Utopia
end YM.ConnectedActivityE6.Blaze.Silica
