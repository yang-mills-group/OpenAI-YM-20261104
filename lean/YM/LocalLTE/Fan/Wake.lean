import YM.LocalLTE.Fan.Dime
/-! Real + generated primitive power balances. coefficient geometry hypothesis only for retained model (no fitting). -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ κ k: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
-- Passed branch. E.any shape. Heights mandatory.
open LocalLTE.FrameBox
def TellerF (R:Rep G f) (β κ:ℝ) (n q:ℕ)(φ:ℝ)(m:ℕ):Prop:= (∃ j≤ n, FrameBox.Polynomial j κ (R.activities.reg m).site (pie q) (R.activities.E m))∧ R.p.supBounds (R.activities.reg m).site (R.activities.reg m).support (R.activities.E m) (φ*β^(chip q+slack))
-- prices are site lease kept separate.
def Breed (R:Rep G f)(r:ℕ→ℕ)(φ:ℕ→ℝ)(β κ:ℝ)(N i J:ℕ):Veil c f→Prop:=Sum.elim (fun m=> r m ≤ J ∧ TellerF R β κ N (r m) (φ m) m) (Sum.elim (fun j=>(R.path.cubic j.2.2).length ≤ i)
     (Sum.elim (fun j=>(R.path.quartic j.2.2).length ≤ i) (Sum.elim (fun j=>(R.path.loop j.2.2).length ≤ i) fun _=>True)))
lemma wagers (X:Coat T F)(hH:Cash W s a L Q o t T R)(he:X.x=s)(hp:X.width=o.K)(p:Disk G c)(r:ℕ→ℕ)(φ:ℕ→ℝ)(b:Air f G)(hβ:1≤B)(hI:B= betaF G s L)(i : Veil c f) {N I n:ℕ}(hT:Breed R r φ B κ N I n i) (hh:(timeΛ X p).manifest)(hQ : Q.rate < mini) (h₂:R.p.threshold^2 ≤ B^(-claw)*B^mini)(h₃:R.beta* R.p.threshold^3 ≤ B^(-claw)*B^mini):
    |vows X R Q o.a p b i| ≤ fisc R B φ i * B^(levy r i):=by
  apply stakes X hH he hp p r φ b hβ hI i _ hh hQ h₂ h₃; intro k hk e U
  let A:= R.activities.reg k; have hp: TellerF R B κ N (r k) (φ k) k:= ((show _ ∧ TellerF R B κ N (r k) (φ k) k from (show Breed (c:=c) R r φ B κ N I n (Sum.inl k) from hk ▸ hT))).2
  by_cases he : Healthy R.p.threshold A.support U
  · rw [Activities.regularOccurrence,masked_eq _ _ _ _ he]; exact hp.2.2 U he [] (Nat.zero_le _) (by simp)
  rw [Activities.regularOccurrence,masked_ne _ _ _ _ he,abs_zero]; exact hp.2.1

set_option maxHeartbeats 650000 in
lemma stars {P:Teller G} (L:Side)(D:Patch)(hd:D.Branches P.bind G){d p :ℝ→ℝ}{N I :ℝ→ℕ}(Q:YM.ConnectedActivityE6.Target G P)(W:ℝ)(o:Target.Order G W)(j m:ℕ)(h₁:1≤j)(hW: -(1/2:ℝ) ≤ v)(h: v<0)(hp: Rate G L v p)(hp': ∀ᶠ x:ℝ in atTop,0≤p x)(hk:Reliable G κ k)(hd':Rate G L 0 d)(hi:Rate G L 0 fun t=>(I t:ℝ))(hN:Rate G L 0 fun t=>(N t:ℝ)):
   ∀ᶠ t in atTop, let B:=betaF G t L
   ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D→ ∀ (R:Rep G f) (μ σ:ℝ) (_H:Cash W t μ L Q o σ T R)(F:Forest S.ratio)(X:Coat T F), X.x=t→ X.width=o.K→∀ (r:ℕ→ℕ)(φ:ℕ→ℝ)(z:Air f G), (∀ i, |z i| ≤ |d t|)→∀ (x:Disk G c)(i:Veil c f),‖x‖< p t → Breed R r φ B κ (N t) (I t) m i →
    Brush j ((fisc R B φ i)*B^(jumpP r i)) 1 (fun p=> coming Q.table R X p z i) x:=by
  have hx:= Rate.mul_left (Rate.hat (G:=G) (L:=L)) 2
  obtain ⟨V,hV,H⟩:= tassels L D hd Q o j 3 h₁ hW h hp hp' hx hd' hi
  obtain ⟨V',hV',H'⟩:= tassels L D hd Q o j 4 h₁ hW h hp hp' hx hd' hi
  obtain ⟨V₀,hV₀,H₀⟩:= tassels L D hd Q o j 2 h₁ hW h hp hp' hx hd' hi
  choose R HR ha using fun i:Fin (m+1)=> field_fuel L D hd Q o j (pie i.val) h₁ hW h hp hp' hk hd' hN
  obtain ⟨P',hp₁,hP⟩:= vaulted L D hd Q W o j h₁ hW h hp hd' hp'
  obtain ⟨A,hA,hP'⟩:= freezeBase L D hd j h₁ o.f h hp hp'
  obtain ⟨K,hK,hK'⟩:= sunlit Q L D hd o j h₁ hW h hp hd' hp'
  have hs : (1:ℝ)< -claw+(mini+3):= by norm_num [claw,mini]
  have hB : (1:ℝ)+0< mini+3:= by norm_num [mini]
  filter_upwards [H,H',H₀,hP,hP',hK',eventually_all.mpr ha,hV _ hs,hV' _ hs,hV₀ _ hs,(hx.mul hp₁) _ hB,hA (mini+3) (by norm_num [mini]),hK (mini+3) (by norm_num [mini]),eventually_all.mpr (fun i=> (HR i) ((1/2:ℝ)*pie i.val+slack) (by unfold slack; linarith)), (YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with t h h' h₀ hg hg' hk' H hv hv' hV₀ ha hA hK hr hB₀ B c f S T hS R μ σ H' F X hX he r φ z hz x i hx hT
  have hθ:= H'.laws.data; have he':= H'.laws.intake
  have hh := he'.window; rw [hθ.funds.length_eq] at hh
  have hB:0<B:=zero_lt_one.trans_le hB₀
  have hF: |-Raw.orientation| ≤ 1:=by rw [abs_neg,abs_of_pos orientation_range.1]; exact orientation_range.2
  have hΛ:|-R.beta*Raw.orientation| ≤ 2*B:=by rw [show -R.beta*orientation=R.beta*(-Raw.orientation) by ring,abs_mul,abs_of_pos he'.positive]; exact (mul_le_of_le_one_right he'.positive.le hF).trans hh.2
  rcases i with i | i | i | i | i
  · obtain ⟨hE,⟨m',hm',h⟩,hσ⟩ := (show _ ∧ (TellerF R B κ (N t) (r i) (φ i) i) from hT)
    let v:Fin (m+1):=⟨r i,by change r i≤ m at hE; omega⟩
    have hv:= H v c f S T hS μ σ hθ F X hX he z hz x hx _ m' _ _ _ hm' h (show R.p.threshold=Pressure.fiery G t L from he'.received.temp.trans (hθ.funds.length_eq ▸ rfl)) ⟨_,hσ⟩
    apply hv.opposite.climb _ le_rfl
    refine (mul_le_mul_of_nonneg_left (hr v) hσ.1).trans_eq ?_
    change φ i*B^(chip _+slack)* B^(1/2*(pie (r i):ℝ)+slack)= φ i* B^((chip _+slack)+(1/2*(pie (r i):ℝ)+slack)); rw [mul_assoc,← Real.rpow_add hB]
  · apply (h _ _ S T R.path.cubic hS _ _ hθ F X hX he z hz x hx.le i _ (by exact_mod_cast (show _≤I t from hT)) hΛ).climb _ le_rfl
    change _≤ (R.path.cubic i.2.2).magnitude* B^(-claw)* B^(mini+3); rw [mul_assoc, ← Real.rpow_add hB]; exact mul_le_mul_of_nonneg_left hv (sum_nonneg (fun _ _=>abs_nonneg _))
  · apply (h' _ _ S T R.path.quartic hS _ _ hθ F X hX he z hz x hx.le i _ (by exact_mod_cast (show _≤I t from hT)) hΛ).climb _ le_rfl
    change _≤ (R.path.quartic i.2.2).magnitude* B^(-claw)* B^(mini+3); rw [mul_assoc, ← Real.rpow_add hB]; exact mul_le_mul_of_nonneg_left hv' (sum_nonneg (fun _ _=>abs_nonneg _))
  · apply (h₀ _ _ S T R.path.loop hS _ _ hθ F X hX he z hz x hx.le i _ (by exact_mod_cast (show _≤I t from hT)) (hF.trans (by change 1≤2*B; change (1:ℝ) ≤ B at hB₀; linarith))).climb _ le_rfl
    change _≤ (R.path.loop i.2.2).magnitude* B^(-claw)* B^(mini+3); rw [mul_assoc, ← Real.rpow_add hB]; exact mul_le_mul_of_nonneg_left hV₀ (sum_nonneg (fun _ _=>abs_nonneg _))
  change Brush j (1*B^(mini+3)) _ _ _; rw [one_mul]; rcases i with i | i | i
  · have he:=hg _ _ S T hS _ _ hθ F X hX he z hz x hx.le i
    apply (he.smul (-R.beta* Raw.orientation)).climb _ le_rfl; exact (mul_le_mul_of_nonneg_right hΛ he.nonneg).trans ((le_abs_self _).trans ha)
  · exact (hg' c f S T hS hθ.funds F X hX (hθ.localP F X.blank hX he (X.bowed (temp_nonneg _))).sails.scale x hx.le i).climb ((le_abs_self _).trans hA) le_rfl
  exact (hk' c f S T hS _ _ hθ _ X hX he z hz x hx.le i).climb ((le_abs_self _).trans hK) le_rfl

lemma dimes {P:Teller G}(Q: YM.ConnectedActivityE6.Target G P)(L : Side)(W:ℝ)(o:Target.Order G W)(hQ: Q.rate< Pastel.mini):∀ᶠ t in atTop,
  ∀ (c f:Side)(S:StepData c f)(T:Tube G S), ∀ (R:Rep G f) (μ σ:ℝ) (_H: Cash W t μ L Q o σ T R)(F:Forest S.ratio)(X:Coat T F), X.x=t→X.width=o.K→ ∀ (p:Disk G c)(r:ℕ→ℕ)(φ:ℕ→ℝ)(b:Air f G)(i:Veil c f)(N I n:ℕ)(κ:ℝ),let β:= betaF G t L
  Breed R r φ β κ N I n i→(timeΛ X p).manifest→ |vows X R Q o.a p b i| ≤ fisc R β φ i * β^(levy r i):=by
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1, ((Rate.hat (G:=G) (L:=L)).mul_left 2|>.mul ((Rate.flame (G:=G) (L:=L)).pow 3)) (-claw+mini) (by norm_num [claw,mini]), ((Rate.flame (G:=G) (L:=L)).pow 2) (-claw+mini) (by norm_num [claw,mini])] with t ht hx hy c f S T R μ σ H F X hX hp p r φ b i N I n κ β hT hP
  have hA:0<β:=zero_lt_one.trans_le ht; have hL:=H.laws.data.funds.length_eq; have he:=H.laws.intake
  apply wagers X H hX hp p r φ b ht rfl i hT hP hQ
  · rw [he.received.temp,hL, ← Real.rpow_add hA]; exact (le_abs_self _).trans hy
  rw [← Real.rpow_add hA]; refine le_trans (mul_le_mul_of_nonneg_right (show R.beta ≤ 2*β from by simpa only [hL,β] using he.window.2) (pow_nonneg R.p.threshold_pos.le 3)) ?_; rw [he.received.temp,hL]; exact (le_abs_self _).trans hx
end YM.LocalLTE.Fan
