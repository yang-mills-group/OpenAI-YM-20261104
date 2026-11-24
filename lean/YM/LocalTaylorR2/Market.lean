import YM.LocalTaylorR2.Income
/-!
 # Issue one calendar probe with an absolute all-vertex, momentum-independent
 local Taylor permit. Adaptation of Das.whittle; exposes ζ optional cost. -/
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
open YM.LocalTaylorR2
structure LocalBookingsR2 (ζ K : ℝ) {H:Cash W s μ L Q o C T R} (Ξ: Utopia H j v d r C' χ) : Prop where
  leases : Sales (radiusB s) Q.relative Q.ε (footprints T R Q.halo (radiusB s)) (fun i=>betaF G s L^lease ζ c f i*Ξ.flair i) (Sum.elim
    (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) K
  logsT : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F:Forest S.ratio) (X: Coat T F)
    (A: E→ Config G c) (b:E→ Directions G f) (z: E→ Air f G) (y:E) (Z: Air f G),
    X.x=s → X.width=o.K → X.χ=χ → X.manifest → Mode A y j v → Clutch X Z o.a R.beta d y j A b z →
    ∀ i:Coat.LogIndex c f, Brush j (Ξ.goalsL i) (r*spanW T R X.B Q.halo (YM.LocalTaylorR2.Port.identityLog i))
        (fun y=> logMoment (vary X (A y)) o.a R Q.table (b y) (X.input (worldZ X R.beta Z)) (z y) i) y
namespace Utopia
lemma leasedUtopiaR2 (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val → ∀ (t ζ : ℝ), -(1/2:ℝ)<t → t<Q.rate → 0≤ζ →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0 < W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤v x) → Rate G L (-(1/2)) w → ∃ (C':ℝ) (r q:ℝ→ℝ), 0≤C' ∧ Rate G L 0 r ∧ Rate G L t q ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T → ∀ (R:Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),
      ∃ Ξ: Utopia H i (v x) (w x) (r x) C' χ, LocalBookingsR2 ζ (q x) Ξ := by
  obtain ⟨n,hn⟩:= Clutch.incomeR2 P Q
  refine ⟨n,fun L hL t ζ hT ht hζ D hd i χ W hw μ hm o v w hv hwV hW=>?_⟩
  obtain ⟨C,hC,hΨ⟩:= Clutch.chimney P D L hd o.K o.γ W o.a χ i Q.table_exists hv hwV hW μ o.indexPay o.f o.large hw o.gamma
  obtain ⟨B,J,hB,hJ,hv',h⟩:= hn L hL t ζ hT (ht.trans Q.stop) hζ D hd i χ W o v w hv hwV hW
  obtain ⟨A,hA,hy,hQ⟩:=Clutch.ash G L χ i hW hv W o.a Q.halo (by have h:=Q.buys; omega)
  obtain ⟨Y,hY,hF⟩:= Coat.alarm_bills (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) P L (2*(t-ζ)-1) (half_pos o.rare)
  let g x:= betaF G x L ^ (t-ζ); let Z x:= B x+A x; have hZ x:1≤Z x:= (hv' x).trans (le_add_of_nonneg_right (hy x))
  have hp:0≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  let u := Coat.topStorm D+1; have hu : 0 ≤ u := by unfold u; linarith [topStorm_one D]
  obtain ⟨b,hb,hH⟩:= exponent_fee G L Q.halo Q.relative Q.ε t u hp (fun x=> betaF G x L^t) Rate.power
  refine ⟨C,Z,_,hC,hB.add hA,hJ.add (hJ.add hb),?_⟩
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hΨ,h,hQ,hF,hY (2*(t-ζ)) (by linarith),Q.pay_for L hm hC,(hJ.add (hJ.add hb)) Q.rate ht]
    with x hLE hΨ h hQ he hV hA hv c f S T hS hF R C' H
  have hΓ:= H.laws.data; have hh:= H.laws.intake
  have hΘ: 0<betaF G x L:=by have he:=hh.height; rw [hΓ.funds.length_eq] at he; linarith
  have hg:0≤g x:= by unfold g; positivity
  have h' := (hΓ.localP)
  obtain ⟨V,y,H₀,Hf,H'⟩:= h _ _ S T hΓ.funds hS hF h' hΓ.access R hh
  have hΞ:=hH x c f S hΓ.funds.length_eq (by have h:= hΓ.room.sight; omega) (mul_nonneg hu (Real.rpow_nonneg hΘ.le t))
  let H'' (p:ConnectedActivityE6.Alphabet c f):= betaF G x L^lease ζ c f p*rates V y (u*g x) p
  have hh' : Sales (radiusB x) Q.relative Q.ε (footprints T R Q.halo (radiusB x)) H'' (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (J x+(J x+b x)):= by
    have hz:= Hf.together (H₀.together hΞ)
    convert hz using 1; · rfl
    · funext i; rcases i with i|i|i <;> simp only [lease,rates,H'',Sum.elim]; rw [mul_left_comm,show betaF G x L ^ ζ * g x=_ from adjust hLE]
  refine ⟨⟨V,y,u,hu,g x,hg,hF,hZ x,(by rw [hΓ.funds.length_eq]; exact hA R.beta (hΓ.funds.length_eq ▸ hh.window.1)),
    (loosen (leaseNN hζ) hLE hh').raise ((le_abs_self _).trans hv),?_,?_⟩, hh',?_⟩
  · intro E _ _ _ F X A' v' w' z q ht hX hχ hZ' hM hp F' k p hv
    have ht' := h' F X ht hX hZ'

    obtain ⟨hL,hK⟩:=H'.stamina E F X A' v' w' z q ht hX hχ hZ' hM hp
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
    · exact (hL p).2.climb le_rfl hv
    unfold u; rw [← hS]; refine (hQ c f S T F X R ht hχ hΓ.funds.length_eq
      (show 0<W*X.t from mul_pos hw ht'.sails.room.fiery) _ q z A' v' w' hp hM p k _).climb le_rfl ?_
    apply le_trans _ (mul_le_mul_of_nonneg_right (show A x ≤ Z x from le_add_of_nonneg_left (zero_le_one.trans (hv' _))) ha)
    apply le_of_eq; unfold twigs lengths; simp
    exact Or.inl rfl
  · intro F X ht hK _ hp K
    have hV' : betaF G x L^(2*(t-ζ))=g x^2 := by unfold g; rw [mul_comm, Real.rpow_mul hΘ.le, Real.rpow_two]
    exact (he.2 c f S T F X ht hΓ.funds.length_eq (h' F X ht hK hp).sails R (ht.symm ▸ hh) K).trans
      (pow_le_pow_left₀ he.1 (((le_abs_self _).trans hV).trans_eq hV') _)
  -- insert unmarked logs at absolute costs as well (at same Clutch pace)
  intro E _ _ _ F Y y' w' z' z Y' hm hq hχ hl hM hA i
  have hw:= (H'.stamina E F Y y' w' z' z Y' hm hq hχ hl hM hA).1 i |>.1
  have hh':0≤ twigs R T Y.B Q.halo (Sum.inr (Sum.inl i)):= add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact hw.climb le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hy x)) hh')
end Utopia
end YM.ConnectedActivityE6.Blaze.Silica
