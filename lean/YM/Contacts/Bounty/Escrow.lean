import YM.Contacts.Terrain.Cardinal
/-! # Two forms of lifetime purchase needed for invoices, actual and auxiliaries.
 Ratio requirement independent of POST choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Terrain
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Beam Stained Shield
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    (H : Cash W s μ L Q o α T R) {p : BudgetPoint} {χ : Chi}
open JointLoad JointLoad.Heir
abbrev jetty (Q : YM.ConnectedActivityE6.Target G P) (K:ℕ) := (Height.housing K Q).choose
variable (K:ℕ) (Z:JointLoad.Heir.Record) (i₀ j n:ℕ) (Y':Libretto G i₀) (P L κ χ Q) (U:Q.Expense) (g:ℝ) (C ζ C' a:ℝ)
-- site.Z
abbrev AxPure (s:ℝ):= ∀ c f S (T:Tube G (c:=c) (f:=f) S), Works P L s S T → Stamp T→∀ (R:RG.Rep G f) (H:Cash W s μ L Q o C T R) (p: BudgetPoint), p.B=radiusB s→p.power=n→preExponent p≤U.earn→p.threshold=Pressure.temp s→p.order≤j→∀ (Δ:ℕ→ Prop) (U':H.fragrances→Prop),Toll R Δ (incomingE G L s) 0 →(∀ i,U' i→ ¬Terrain.Lantern H K Δ i)→ Make H p χ U' (g*betaF G s L^(-ζ:ℝ))
lemma bigTown (_hh :3 ≤ K)(hL : jetty Q K ≤ L.val) (hm:0<μ)(hw:0<W) (hg:0<g) (hu:U.wanting < -(3/8:ℝ))(hk:ζ < K*(3/8:ℝ)-3) : ∀ᶠ t:ℝ in atTop, AxPure (o:=o) (μ:=μ) L P Q χ K j n U g C ζ t:= by
  let v:=g/2; have hv:0<v:=half_pos hg; have hE := (housing K Q).choose_spec L hL U W μ C o hw hm j n χ; filter_upwards [hE,cruising Q U L hm j n hu v hv,protracted K Q L hm,δratio (G:=G) (L:=L),windage (G:=G) K L ζ hk hv,(YM.Work.E09.betaF_growth G L).eventually_gt_atTop 1] with s hX hq hv' hK hz hf c f S T H hT R NN p hr hp he hP hO Δ U' hT' hL'
  obtain ⟨hh₁,hh₂,hh₃,h⟩:=hq; let a:=betaF G s L; let w:=a^(-(ζ:ℝ)); let f₀:=grow G L s^3; let V:=grow G L s; have hl:0<V:=zero_lt_one.trans_le hh₁; have ha:1<a:=hf; let τ:=w/(2*f₀); have hh':Toll R Δ (incomingE G L s) τ:= by obtain ⟨b,hb,hB,hC⟩:=hT'.wage; refine ⟨b,hb,hB,fun i=>Cost.enlarge (hC i) ?_⟩; unfold τ w f₀; change 0≤_/ (2* V^3); positivity
  obtain ⟨η,Ω,hΩ,hω,hΘ,hD,hΩ'⟩:= hh'.seal (by unfold τ w f₀; change 0<_/(2* V^3); positivity) (by unfold incomingE; positivity); obtain ⟨C',d,v',t,A,b,r,B,q,i',k,⟨N,hN⟩,hr',hh⟩:= hX.2 c f S T H hT R NN Ω hΩ hΩ'
  obtain ⟨hI,hA,hZ⟩:=h B i' k hr' N.balance hh; have hS:=spacious N hh₁ hΩ hN n hI hv' hX.1 hh₃ hA; let vH:=2*f₀*v*incomingE G L s
  have hf' :0<f₀:= pow_pos hl _; have hU:= pow_le_pow_right₀ hh₁ (Nat.zero_le K)
  have hp':= spacious N hh₁ hΩ hN n hI (hU.trans hv') (hU.trans hX.1) hh₃ hA
  have hs' x := budget_loosen (hp' x) (show _≤ vH from ?_); swap; · simp only [pow_zero,inv_one,one_mul]; unfold vH; have h:=mul_le_mul_of_nonneg_left hZ hf'.le; rw [show 2*f₀*v*incomingE G L s=f₀*(v*(2*incomingE G L s)) by ring]; apply Eq.trans_le ?_ (h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hv.le) hf'.le)); change _ = f₀*(f₀⁻¹*_ * _); field_simp
  have hS' x:= budget_loosen (hS x) ((le_trans ?_ hz)); swap; · have h:=mul_le_mul_of_nonneg_left hZ (show 0 ≤ (V^K)⁻¹*V^3 by positivity); convert h using 1; field_simp; unfold V; ring
  have hu' := frost NN p χ _ N hP hr he hO hp.le 1 (v*w) (fun _=>True) (fun i _=>one_le_prod (s:=univ) (f:=fun k=> feel Ω (S:=S) (i.2 k).val) (fun k _=> feel_pos hΩ _)) zero_lt_one hS'
  have hv₀ := frost NN p χ _ N hP hr he hO hp.le η vH (latent NN Δ) (paidit NN hΩ hω) hΘ hs'
  apply Cap.raise (nextK NN p χ _ _ (shed NN p χ _ _ hu' hv₀) ?_)
  swap; · intro i hi x hx; by_contra! ht; exact hL' i hi (sprite NN K hx (ht.2 (Or.inl (Nat.zero_le _))) ht.1)
  rw [inv_one,one_mul]; change _≤ g*w; unfold vH; rw [show η⁻¹ * _ = (2*f₀*v) * (η⁻¹ * incomingE G L s) from (by ring: η⁻¹*(2*f₀*v*incomingE G L s)=_)]; refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hD (show 0 ≤ 2*f₀*v from by positivity))).trans_eq ?_; unfold τ v; field_simp; ring
-- duplicate with prepared pre knob
lemma stately (hhG:G.Simple) (hZ:Z.ε ≤1/4) (hκ:2≤ i₀) (hv:i₀≤j) (hw:3 ≤ K) (hm:0<μ)(he:0<W)(hu:U.wanting < -(3/8:ℝ))(hg:0<g)(ζ:ℝ) (hζ:(ζ:ℝ) < ((K:ℝ)* (3/8) -(3:ℕ))) (hL : jetty Q K ≤ L.val) :  ∀ (Z': Patch), Z'.Branches P.bind G → ∀ ℓ a C C', 0≤a → ∀ᶠ s in atTop, Palace (μ:=μ) (o:=o) L P Q χ K Z i₀ j n Y' U g Z' ℓ a C C' ζ s := by
  have hm':= (Height.housing K Q).choose_spec
  intro Z' hT ℓ a C c' ha
  obtain ⟨E,hE,hF⟩:= Brim.apogee G hhG P L Z' hT n i₀ Y' Z hZ hκ χ Chi.canonical W o a ℓ ha
  filter_upwards [hF,hm' L hL U W μ C o he hm j n χ,Height.cruising Q U L hm j n hu g hg, Height.protracted K Q L hm,δratio (G:=G) (L:=L),windage (G:=G) K L ζ hζ hg,hE.below (by norm_num) g hg] with s hΞ hH hx hv' hK hy hu c f S T hS hs he R H p hr hp ht hv'' hA hC hV hO hO' hP hJ Δ τ U' hτ ht' hL'
  obtain ⟨η,Ω,hΩ,h,hΘ,hD,hΩ'⟩:= ht'.seal hτ (by unfold incomingE; positivity)
  obtain ⟨C', d, v', t, A, b, r, B, q, i, k,⟨ N,hN⟩,hr',hh⟩:= hH.2 c f S T hs he R H Ω hΩ hΩ'
  obtain ⟨hh',hh'',hh''',hh⟩:= hx
  obtain ⟨hI,hY,hE⟩:= hh B i k hr' N.balance (by assumption)
  obtain ⟨b₁,hb,hb',hB⟩:= ht'.wage
  have hS':= spacious N hh' hΩ hN n hI hv' hH.1 hh''' hY
  have hQ:= spacious N hh' hΩ hN n hI hh'' ((pow_le_pow_right₀ hh' hw).trans hH.1) hh''' hY
  let u:=g*betaF G s L ^ (-ζ:ℝ); let v:=2*g*incomingE G L s
  have hQ' z:= budget_loosen (hQ z) (hE.trans (show g*δE s ≤ v from (mul_le_mul_of_nonneg_left hK hg.le).trans_eq (by unfold v; ring)))
  have hS'' z:= budget_loosen (hS' z) (le_trans (b:=(grow G L s^K)⁻¹*grow G L s^3*(g*δE s)) (show _ from ?_) hy); swap
  · have hv : 0<grow G L s:=zero_lt_one.trans_le hh'; have hK:= mul_le_mul_of_nonneg_left hE (show 0 ≤ (grow G L s ^ K)⁻¹*grow G L s^3 by positivity); convert hK using 1; field_simp --
  have hq: Pics H Δ p Z Chi.canonical Chi.canonical χ 1 a (c'/L.val*τ) (|E s| *τ) := hΞ c f S T hS hs R Q μ C H p hr hp ht hv'' c' hA hC hV j hv _ _ _ _ _ _ _ _ _ _ N _ _ _ _ _ (fun _=> kcop) (fun i=> ⟨hb i, R.p.loMass _ _ (hb i|>.1) |>.trans (by simpa using budget_single (hb' (R.activities.reg i).site) i)⟩) hB
  have hF':= tall H p χ U' Δ K N hP hr hO hJ hp.le u v Ω η hΘ hΩ h hS'' hQ' Z Chi.canonical Chi.canonical a hO' _ _ _ hq hL'
  refine Cap.raise hF' ?_
  change _≤ u+_; unfold v; rw [inv_one,one_mul]; apply add_le_add_right
  have he:= mul_le_mul_of_nonneg_left hD (show 0 ≤ 2*g by positivity); nlinarith only [he,mul_le_mul_of_nonneg_right hu hτ.le]
end YM.PhysicalNext.Repeat.Terrain
