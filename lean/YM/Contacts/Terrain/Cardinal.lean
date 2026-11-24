import YM.Contacts.Terrain.Long
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
/- Quantities at tuner post-roll. Dynamic, full option of projection & arrays
 already chosen. Maxmail. Mesh docket propagation later. No lower bound on the
 incoming error (τ); a tiny positive number is OK. Works uniformly at ALL torus periods.
 These are all unmasked `Song.sequence` bounds (`Make`) for regular automata.
 -/
open JointLoad JointLoad.Heir
structure Toll (R:RG.Rep G f) (Δ:ℕ→Prop) (A τ:ℝ) : Prop where
  wage : ∃ b:ℕ→ℝ, (∀ i,R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (b i)) ∧
      (∀ u:Site f, SumBudget (fun i=> if (R.activities.reg i).site=u then R.p.mass (R.activities.reg i).support (b i) else 0) A) ∧
      (∀ u:Site f, SumBudget (fun i=> if (R.activities.reg i).site=u then R.p.mass (R.activities.reg i).support ((selectK Δ*b) i) else 0) τ)
-- given separate τ, choose min.A later
lemma Toll.seal {A τ:ℝ} {Δ:ℕ→Prop} (h : Toll R Δ A τ) (hv:0<τ)(hh:0≤A) : ∃ (η:ℝ) (Ω:ℕ→ℝ), (∀ i,1≤Ω i) ∧ (∀ i,Δ i → η≤Ω i) ∧ 0<η ∧ η⁻¹*A ≤ τ ∧ Sealed Ω R (2*A) := by
  obtain ⟨b,hc,hp,hT⟩:=h.wage
  let e:=A/τ; let η:=1+e; have he:0≤e:=by unfold e; positivity
  let Ω i:=1+e*selectK Δ i; have hy:0<η:=by unfold η; positivity
  refine ⟨η,Ω,fun i=>le_add_of_nonneg_right (mul_nonneg he kcop),fun i h=>?_,hy,?_, ⟨⟨b,hc,fun i=>?_⟩⟩⟩
  · simp [η,Ω,selectK,h]
  · rw [inv_mul_le_iff₀ hy]; unfold η e; rw [add_mul]; field_simp; linarith
  have hE:= budget_plus (hp i) (budget_scale he (hT i)); convert hE using 1
  · ext w; simp only [BudgetPoint.mass,Pi.mul_apply,Ω]; split_ifs <;> ring
  unfold e; field_simp; ring
lemma δratio : ∀ᶠ s in atTop, δE s ≤ 2*incomingE G L s := by
  let z (x:ℝ):= betaF G x L
  have ha (x:ℝ) : z x=x+G.slopeConstant*Real.log (L.val:ℝ) := rfl
  have hh (x:ℝ) : incomingE G L x=δE (z x) := rfl
  filter_upwards [eventually_gt_atTop (0:ℝ), Delay.shift_pos G L, eventually_ge_atTop (4*G.slopeConstant*Real.log (L.val:ℝ))] with x hx hV h
  -- gap ratio sqrt.Could choose clumsy pow².R.
  let y:= z x
  have he:y ≤ (1+1/4)*x:= by unfold y; rw [ha]; linarith
  have he': 0<y:=hV
  let w(x:ℝ):= x^(-(11/10):ℝ); have hZ {x} (h:0<x): δE x=w x:= by unfold δE Clock.gap w; rw [Real.sqrt_eq_rpow,← Real.rpow_neg h.le,← Real.rpow_mul h.le]; norm_num
  rw [hh,hZ hx,hZ hV]
  change w x≤2*w y
  have hz:w ((1+1/4)*x) ≤ w y:=Real.rpow_le_rpow_of_nonpos he' he (by norm_num)
  apply le_trans _ (mul_le_mul_of_nonneg_left hz (by norm_num))
  unfold w; rw [Real.mul_rpow (by norm_num) hx.le, ←mul_assoc]
  apply le_mul_of_one_le_left (by positivity); apply le_trans ?_ (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) (show (-(2:ℕ):ℝ) ≤ -(11/10:ℝ) by norm_num)) (by norm_num))
  rw [Real.rpow_neg (by norm_num)]; norm_num

lemma windage (w:ℕ)(L : Side)(ζ:ℝ)(hh:(ζ:ℝ) < ((w:ℝ)* (3/8) -(3:ℕ))) {g:ℝ} (hg:0<g) : ∀ᶠ s in atTop, (grow G L s ^ w)⁻¹*grow G L s^3*(g*δE s) ≤ g * betaF G s L ^ (-ζ:ℝ) := by
  let B:= grow G L; let C:=(3/8:ℝ); have he := Rate.power (G:=G) (L:=L) (a:=C)
  have h : Rate G L (-(C*w)) (fun s=> (B s^w)⁻¹) := by
    apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; unfold B grow C; rw [Real.rpow_neg hx.le,Real.rpow_mul hx.le]; norm_cast
  have hh':= ((h.mul (he.pow 3)).mul (Rate.const (G:=G) (L:=L) 1)) (-ζ) (by unfold C at *; norm_num1 at *; linarith)
  filter_upwards [hh',Delay.shift_pos G L,eventually_ge_atTop (1:ℝ)] with s h hg' hw
  have hP:0<s:= zero_lt_one.trans_le hw; have hG:0<grow G L s:=Real.rpow_pos_of_pos hg' _
  have hu : δE s ≤ 1:= by rw [show δE s=s^(-(11/10):ℝ) from (by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hP.le,← Real.rpow_mul hP.le]; norm_num)]; exact Real.rpow_le_one_of_one_le_of_nonpos hw (by norm_num : -(11/10:ℝ) ≤ 0) |>.trans le_rfl
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hg.le) (by positivity : 0 ≤ (grow G L s^w)⁻¹*grow G L s^3))
  rw [mul_one, mul_comm _ g]; apply mul_le_mul_of_nonneg_left _ hg.le
  simpa only [mul_one,grow,B,C] using (le_abs_self _).trans h

variable (K:ℕ) (Z:JointLoad.Heir.Record) (i₀ j n:ℕ) (Y':Libretto G i₀) (P L κ χ Q) (U:Q.Expense) (g:ℝ)

/-- P=(same Patch D) ruling pre/post L. e.g. gather extra from gates. -/
def Palace (Z':Patch)(ℓ:ℕ)(a C C' ζ s:ℝ):= ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=Z' → Works P L s S T → Stamp T → ∀ (R:Rep G f)(H:Cash W s μ L Q o C T R)(p:BudgetPoint), p.B=radiusB s → p.power=n → Plays Y' Z p R.p P T s → Q.halo+5 ≤ℓ → Release.accepts ℓ R.p.supportExponent a L → Release.Quotation Y' n ℓ R.p.supportExponent a C' → Lute.Plented Y' Z p R.p L ℓ s (gStep R.beta) → preExponent p ≤ U.earn → preExponent p ≤ a → p.threshold=Pressure.temp s → p.order ≤ j → ∀ (Δ:ℕ→Prop)(τ:ℝ)(U': H.fragrances→Prop), 0<τ → Toll R Δ (incomingE G L s) τ → (∀ i, U' i → ¬Terrain.Lantern H K Δ i) → Make H p χ U' (g*(betaF G s L ^(-ζ:ℝ))+ (2*g+C'/L.val+g)*τ)
-- lend post uniform valuations
lemma grandeur (hhG:G.Simple) (hZ:Z.ε ≤1/4) (hκ:2≤ i₀) (hv:i₀≤j) (hw:3 ≤ K) (hm:0<μ)(he:0<W)(hu:U.wanting < -(3/8:ℝ))(hg:0<g)(ζ:ℝ) (hζ:(ζ:ℝ) < ((K:ℝ)* (3/8) -(3:ℕ))) : ∃ m:ℕ, ∀ (L:Side), m≤L.val → ∀ (Z': Patch), Z'.Branches P.bind G → ∀ ℓ a C C', 0≤a → ∀ᶠ s in atTop, Palace (μ:=μ) (o:=o) L P Q χ K Z i₀ j n Y' U g Z' ℓ a C C' ζ s := by
  obtain ⟨m,hm'⟩:= Height.housing K Q
  refine ⟨m,fun L hL Z' hT ℓ a C c' ha=>?_⟩
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
