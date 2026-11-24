import YM.Frontier.Tuning.TiltTogether
/-! Tilted angular Arc estimates, after true unscaled real probability budget. Integral
pays one *whole* catastrophe together with facescale powers on complete support, leaving
an account for summing across typed molecules. Still price-side before an actual
contour identity/germ or assembly; no period-dependent threshold. Uses Flux.launch's
walksW/real proof technique for the marginal moment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.VectorTilt
open TiltTogether Footage YM.Frontier.Tuning.Voice HeldBurst DensityTilt
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster PhysicalNext.Repeat.Height Held ClockShift TwoMotion AngularReceipt Flux Shield Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R A : Rep G f} {X : Coat T F} {x :Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {z:E}
variable {H0 a C α Z β γ d η ε σ W s b μ r p q v : ℝ} {j n l : ℕ} {Q : ConnectedActivityE6.Target G P}
variable {o : Target.Order G W}
variable {χ:Chi}
local notation "b₁" => betaF G s L
local notation "M₀" => radiusB s
set_option maxRecDepth 8192
set_option pp.proofs false
set_option quotPrecheck false
set_option maxHeartbeats 2000000

variable {H: Cash W s μ L Q o H0 T R}
variable {C' : ℝ}
variable (P' : Pocket H A j v q C α d γ χ)



open Mixed
open Reserves
-- Half-set reserve weights. `cap l` independent of output ordinal; increase bought envelope
-- power to handle arbitrarily many fixed angular probes, NOT one reserve per test jointly.
def heated (P':Pocket H A j v q C α d γ χ) (l:ℕ) (p:Molecule S):ℝ:=if H.ticketsP 0 0 0 p then
    (∏ i∈p, Footage.tag P' P'.rad i)*Real.exp (Q.ε*H.shapeW p)*(1+H.shapeW p)^l else 0
local notation "Π" => Q.costs L μ (betaF G s L/2) s C
lemma hit (l:ℕ) : Ac.Hit H.unionP M₀ (heated P' l) Q.exp (Reserves.extract (Q.ε/2) l 0 (Π.markSeed*0)*treeYield Π.rootHit Π.q 0):=by
   convert Voice.heatHit S Q.halo M₀ Π _ _ _ _ P'.lives P'.accounts 0 l 0 0 using 1
   · rfl
   · funext p; unfold heated hotSelection; change (if Allowed _ _ _ _ _ _ _ _ _ _ then _ else _) = if _ then _ else _
     have hk : Allowed S Q.halo M₀ H.faresP H.birth (ConnectedActivityE6.lengths T R) 0 0 0 p =
       Allowed S Q.halo M₀ Π H.birth (ConnectedActivityE6.lengths T R) 0 0 0 p :=rfl
     rw [hk];split_ifs <;> first | rfl | skip
     change (∏ t∈p, _) * Real.exp (Q.ε * H.shapeW p) * _ = (∏ t∈p,Footage.tag P' _ t) * (1+H.shapeW p)^l * _
     exact mul_right_comm _ _ _
   all_goals first | rfl | { rw [Nat.cast_zero]; rfl}
lemma root_rate (Q:ConnectedActivityE6.Target G P)(L:Side) (hμ:0<μ) : Rate G L Q.rate (fun s => (Q.costs L μ (betaF G s L/2) s C).rootHit) := (Q.rate_root L hμ (β:=1) (C:=C)).congr (Eventually.of_forall fun _=>rfl)
def WalkBound (H':Cash W s μ L Q o C' T R) (D:ℝ)(l n:ℕ):Prop := ∀ (i V Z : ℝ),1≤Z→0 ≤ i → i ≤ Z*Animals.ballCost (radiusB s)*(Itinerary.density L:ℝ) → V=i*Fintype.card G.ColorIndex →
  (1+i+V+V)^n * (1+V*(2*Real.exp (payE o.eta o.gap o.ample (tubularPrice G L)*(n:ℝ)^2/2))) ≤ |D| * Z^l
-- pay thermal indicator Mark twice (rad^2 entire event)
lemma integrablePrice (X : Coat T F)(hX:X.x=s)(hM:X.manifest)(hk:X.width=o.K)(hχ:X.χ=χ)
   (k κ:ℕ)(B B':ℝ) (p:Molecule S) (he:Ac.Spark H.supportP p) (hp:troupe T R Q.halo M₀ p)(τ:ℂ)
   {D:ℝ} {l:ℕ}
   (hm : WalkBound H D l ((κ+k)*j*2)) :
     let I:= edgesM S (H.unionP p) M₀
     let E(z : F.Slice G × Air f G):=envelope P' B B' k κ τ p (X.wrapY z.1) I z.2
     let θ:=(1+coefficient P' B B' τ)^j
     Integrable E ((F.order G).prod X.dice) ∧ ∫ t,E t ∂((F.order G).prod X.dice) ≤ ((1+|D|)*θ) * heated P' (l+j) p:= by
  intro I E θ; let x' := 1+H.shapeW p; let J:= X.catastrophe (o.ξ/2) R.beta (blaze p); let n:=(k+κ)*j
  have h' :1≤x':=le_add_of_nonneg_right (H.positive_volume p); let e := D; let Ξ:=P'
  let f(z : Air f G):= facescale I z^n; let S':=1+H.shapeW p; let X' z:= J.indicator f z
  let a:=(∏ i∈p, Footage.tag P' 1 i)*Real.exp (Q.ε*H.shapeW p)*θ*S'^j
  have hR:= H.laws.data.localP F X hX hk hM
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p)
  have hθ:0≤θ:=by apply pow_nonneg; have hP:=P'.wide; have hv:=P'.strong; unfold coefficient lumpSum; positivity
  have ha:a≥0 := by unfold a; exact mul_nonneg (mul_nonneg (mul_nonneg (prod_nonneg fun i hi=> Footage.positive P' zero_le_one i) (Real.exp_pos _).le) hθ) (pow_nonneg (zero_le_one.trans hx') _)
  have hQ:MeasurableSet J := Poll.sounded ..
  have hm':=globes I hR.sails (n*2)
  have hV := (globes I hR.sails n).1
  have hTax : Integrable (X': Air _ G→ℝ) X.dice := hV.indicator hQ
  let D':=1+|D|
  have hd: 1≤D':=le_add_of_nonneg_right (abs_nonneg _)
  have hE: ∫ x,X' x ∂X.dice ≤ (D'*S'^l)*Ξ.rad^(blaze p).card := by
    let i':ℝ:= I.card; let V:ℝ:= (lensS I G).card
    have hI: i'≤ S'*ballCost M₀* (Itinerary.density L:ℝ) := by
      have h:= Flux.crewsC H p; rw [H.laws.data.funds.length_eq] at h; apply h.trans; unfold S'; gcongr; linarith
    have hV' : V=i'*Fintype.card G.ColorIndex := by simp [V,i',lensS]
    have hn: (κ+k)*j*2=n*2:=by unfold n; simp [add_comm] -- omega not nonlinear, add_comm
    unfold WalkBound at hm; rw [hn] at hm
    have hp := hm'.2.trans (hm i' V S' hx' (Nat.cast_nonneg _) hI hV')
    have hc : ∫ x,f x^2 ∂X.dice ≤ (D'*S'^l)^2 := by
      unfold f; simp_rw [← pow_mul]; apply hp.trans
      exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans
        (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hd (one_le_pow₀ hx')) (by omega))
    refine Flux.divideC _ f hV _ (by have hv:=one_le_pow₀ (n:=l) hx'; positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X hX hk hχ hM (blaze p)) (pow_nonneg Ξ.awake _) ?_ hc
    unfold f; simp_rw [← pow_mul]; exact hm'.1
  have H₁: E= fun z=>a*X' z.2:= by
    unfold E envelope a; dsimp only [X']; funext i;by_cases hi:i.2∈J
    · change J.indicator (fun _=> _ ) i.2 * _ * _ * facescale _ _^_=_;rw [Set.indicator_of_mem hi,Set.indicator_of_mem hi]; unfold f θ S' n; ring
    change J.indicator (fun _=> _ ) i.2 * _ * _ * facescale _ _^_=_; rw [Set.indicator_of_notMem hi,Set.indicator_of_notMem hi]; ring
  rw [H₁]
  have hhP: Integrable (fun z:F.Slice G × Air _ G=> a*X' z.snd) ((F.order G).prod X.dice) := (hTax.const_mul a).comp_snd _
  refine ⟨hhP,?_⟩; rw [integral_prod _ hhP]; dsimp only; simp_rw [integral_const_mul]; rw [integral_const]; simp only [probReal_univ,one_smul]
  refine (mul_le_mul_of_nonneg_left hE ha).trans_eq ?_
  rw [heated,if_pos ((H.attends _).2 he),paid_event P']; unfold a S' D'; ring
end YM.Frontier.Tuning.VectorTilt
