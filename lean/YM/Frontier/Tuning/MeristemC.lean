import YM.Frontier.Tuning.RecoilIdentity
import YM.Frontier.Tuning.WingC
import YM.Frontier.Tuning.ZestPalette
import YM.Frontier.Tuning.CarryC

/-! Actual integration bounds before period by combining postperiod neighborhood domination with pointwise angular estimates (later). No gluing of masks varying with the draw. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Frontier.Tuning.MeristemC
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Blaze Art Silica Poll Pond Eider Flux Held GlassLog Zest TwoMotion RecoilIdentity Shield DensityTilt PhysicalNext.Repeat.Alabaster
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]{x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {η Y r' Q' W : ℝ} {C : E → Config G c}
variable (H : Glass P X C x j W) {Q:ConnectedActivityE6.Target G P} {R R': Rep G f}
variable (hP : Port P L η r' Q' Y X)
variable (ho : Intake P T X.x R) (ht:Facing R R')(hr:Intake P T X.x R')
variable (J : Finset (Bond f)) {K K' : ℝ} (hK:Canary G K K')(z':Molecule S)
variable {μ S0 C'':ℝ}{o:Target.Order G W}(H0: Cash W S0 μ L Q o C'' T R)

private lemma pref_group (K:ℝ)(τ:ℂ)(V:Config G c)(z:Air f G) : scTilt X τ R J K V z=
    let S:=lensS J G
    Complex.exp (((lensS J G).card:ℂ)/2 * (Complex.log τ-Complex.log R.beta)) * (jacL J X K R.beta V z:ℝ) * (WingC.pencil (τ/R.beta) (circuit S (vary X V).relating) (swim S (course X K R.beta z V)) / (lens₀ (circuit S X.relating) (swim S z):ℂ)) :=by
  dsimp only; rw [scTilt,ComplexSweep.exactPhase,scalp]
  rw [WingC.pencil,Complex.exp_add]; push_cast; ring

include H ht hr hP hK H0
set_option backward.isDefEq.respectTransparency false in
lemma price_region (hX: X.width=o.K) (hS:X.x = S0) (he : 8*o.a*X.t ≤ K/2) (U : Set ℂ) (τ:ℂ→ℂ)(e'f h:ℂ→Payload G f){bM cM cL:ℝ} (hL:0<cL)(hC:0≤cM)
   (hv : ∀ i∈U, ‖τ i‖ ≤ cM ∧ cL ≤ (τ i).re ∧ ‖Complex.log (τ i)‖ ≤ cM ∧ ‖ComplexVertex.logMass Q.table (τ i)‖ ≤ cM)(hf : ∀ i∈U, fans R R' bM (e'f i) (h i)) :
  let a:=o.a; let M:=(F.order G).prod X.dice
  let g i y s:= rotor J K (C y) z' (e'f i) (h i) R (X.wrapY s.1) Q.table a W Q.halo (τ i) s.2
  ∃ B,Integrable B M ∧ ∀ᶠ y in 𝓝 x, ∀ i∈U, Measurable (g i y) ∧ ∀ s, Brush j (B s) 1 (g i · s) y:=by
  intro a M g
  have hO:Intake P T X.x R := hS.symm ▸ H0.laws.intake
  have heq:= H0.laws.data; have hM:= hP.sails
  have ho:=H0.laws.intake.positive
  let A':= lensS J G
  let U' i:=circuit A' (vary X (C i)).relating; let V':= circuit A' X.relating
  have hx: U' x=V' := by unfold U' V'; rw [H.lifts]; rfl
  have hF:= hM.fullC; have hU' : V'.PosDef := hF.submatrix Subtype.val_injective
  have hV:= own_mat hM J
  have hs : Bottom V'⁻¹ (1+payE η r' Q' (tubularPrice G L))⁻¹ := Control.lower_inverse hV.relented hV.weather.1.le hV.fuel hV.symmetry
    hV.ground hV.down.le hV.initial.1
  let X'(t:F.Slice G × Air f G):= X.wrapY t.1; let w t v:= course (X' t) K R.beta t.2 (C v)
  let z(t:F.Slice G×Air f G):= Pond.swim A' t.2; have hZ : MeasurePreserving z M (sweep V') := by
    have hs := (Pond.orbit hF.posSemidef A')
    apply hs.comp (show MeasurePreserving _ M X.dice from _); exact MeasureTheory.measurePreserving_snd
  let Z t v:=Pond.swim A' (w t v)
  obtain ⟨hΞ,hω⟩:= Glass.towers (U:=fun i:F.Slice G × Air f G=> i.2) (Y:=fun i=> i.1) H hM.room hK J ho
  let ζ(i:U×F.Slice G×Air f G):= τ i.1/R.beta
  obtain ⟨B,hB,hk,hPi⟩:= WingC.wingletC (ζ:=ζ) (A:=U') (Z:=fun i=>z i.2) (V:=fun i=>Z i.2) (m:=cL/R.beta) (c:=cM/R.beta) (div_pos hL ho) (div_nonneg hC ho.le) (by
    intro i
    exact ⟨by dsimp only [ζ]; rw [Complex.div_ofReal_re]; exact div_le_div_of_nonneg_right (hv i.1 i.1.2).2.1 ho.le, by dsimp only [ζ]; rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ho]; exact div_le_div_of_nonneg_right (hv i.1 i.1.2).1 ho.le⟩) (hx.symm ▸ hU') (hx.symm ▸ hs) (inv_pos.mpr hV.fuel)
    (fun i j=>H.relate i.val j.val) (hω.via Prod.snd)

  let Qf s:=worldZ (X' s) R.beta s.2; let S' s y:= steer (X' s) K (fun i=> prune K (Qf s i)) (C y)
  let V s i:=vary (X' s) (C i); let T' s:= (X' s).input (Qf s)
  let Z' t y:= sweepZ (V t y) R.beta (S' t y)
  have hw0: Zest S' x j := (H.foreshadow (Y:=Prod.fst) Qf hK).1
  let L' : Directions G f →ₗ[ℝ] Air f G := { toFun t:= WithLp.toLp _ (stand t),map_add' _ _:=rfl,map_smul' _ _:=rfl }
  have hK0: Zest Z' x j := (((hw0.plusminus (H.settles (Y:=Prod.fst) hM.room)).scalar (gStep R.beta)⁻¹).replay L'.toContinuousLinearMap)
  let Ω:=U×F.Slice G×Air f G
  let θ(y:Ω):ℂ:= τ y.1.1
  let Z1(t:Ω) i:=floatC (V t.2 i) R (w t.2 i) Q.table a W (own z') (θ t) Q.halo (e'f t.1.1) (h t.1.1) z'
  have hg0 : 0<a*X.t := mul_pos o.large hM.room.fiery
  have ht':4*a*X.t<Q.table.radius:= by rw [Coat.t,hS,heq.funds.length_eq]; exact heq.covers
  have hw:Zest Z1 x j:=by
    have h:=ZestPalette.heldFlo H (fun i:Ω=>T' i.2) (Y:=fun i=>i.2.1) hM.room (hw0.via Prod.snd) (hK0.via Prod.snd) hO hr ht (k:=own z') Q.halo hg0 ht' Q.table_exists
      (e:=fun i:Ω=>e'f i.1.1) (f':=fun i:Ω=>h i.1.1) (τ:=θ) (vM:=cM) (fun i=>⟨(hv i.1.1 i.1.2).1,(hv i.1.1 i.1.2).2.2.2⟩) (bM:=bM) (fun i=>hf i.1.1 i.1.2) z'
    refine h.congr ?_
    obtain ⟨v,hY⟩:= H.sails
    filter_upwards [Silica.nearby X hK H.lifts hY,H.brews.1] with y hy hT t
    unfold Z1 floatC; dsimp only; refine Finset.prod_congr rfl fun i hi=>?_ 
    obtain ⟨r,s,p,q,_,_,_,_,hr',hq⟩:= hf t.1.1 t.1.2
    have hh' := CarryC.thatches (R:=R) (A:=R') (X:=X' t.2) (a:=a) (W:=W) (O:=Q.table) (k:=own z') (l:=Q.halo) (τ:=θ t) (e:=traitE R R' r s) (f':=traitK R R' p q) (fun _ _=>rfl) (fun _ _=>rfl) ht hO hr (C y) hK
      (show Drivable (X' t.2) K K' (C y) from ⟨hy.good⟩) hg0 he (show _ from hT) hM.room i t.2.2 (Qf t.2) rfl -- ?
    replace hh':=hh'.symm
    rw [← hr',←hq] at hh'
    exact hh'
  let pref(i:Ω):= Complex.exp (((lensS J G).card:ℂ)/2*(Complex.log (θ i)-Complex.log R.beta))
  have hp:Zest (fun (i:Ω) (_:E)=> pref i) x j:= ZestPalette.zexp (ZestPalette.zmul (Zest.still _) (Zest.plusminus (Zest.parallel hC (fun i:Ω=>(hv i.1.1 i.1.2).2.2.1)) (Zest.still _)))
  have hZest:= ZestPalette.zmul (ZestPalette.zmul hp (ZestPalette.zcast (hΞ.via Prod.snd))) hw
  obtain ⟨b,hb,hX'⟩:= hZest.post
  let F' s:= (b*B (z s)*(1+(1+1))^j)
  have ha:Integrable (fun s=> B (z s)) M:= hZ.integrable_comp hB.aestronglyMeasurable |>.2 (hx ▸ hk)
  refine ⟨F', (ha.const_mul b).mul_const _,?_⟩; obtain ⟨v,hΨ⟩:=H.sails
  rw [hx] at hPi
  filter_upwards [hPi,hX', nearby X hK H.lifts hΨ] with y hy hY hT i hi
  obtain ⟨r',m',p0,q0,_,_,_,_,h1,h2⟩:=hf i hi
  rw [show g i y=fun t=>rotor J K (C y) z' (e'f i) (h i) R (X' t) Q.table a W Q.halo (τ i) t.2 from rfl,h1,h2]
  have he : ShellAccess S G X.x W X.width o.γ := hX.symm ▸ hS.symm ▸ heq.access
  refine ⟨RecoilIdentity.borel (O:=Q.table) (l:=Q.halo) (τ:=τ i) (e:=traitE R R' r' m') (f':=traitK R R' p0 q0) (fun _ _=>rfl) (fun _ _=>rfl) ht hO J K (C y) z' hK hT he hr Q.table_exists Prod.fst Prod.snd measurable_fst measurable_snd,?_⟩
  intro s0
  let t:Ω:= (⟨i,hi⟩,s0)
  have hv₁:=hY t
  have hv₂:=hy t
  refine ((hv₁.paints hv₂).trim).shimmy (Filter.Eventually.of_forall fun y'=>?_) |>.climb le_rfl le_rfl
  change rotor J K (C y') z' (e'f i) (h i) R (X' s0) _ _ _ _ _ _= (pref t * _ * Z1 t y') * _
  rw [RecoilIdentity.rotor,pref_group]; dsimp only; change pref t*(jacL J (X.wrapY t.2.1) K R.beta (C y') t.2.2:ℂ)*(WingC.pencil (ζ t) (U' y') (Z t.2 y') / (lens₀ V' (z t.2):ℂ))*Z1 t y' = (pref t*_*Z1 t y')*_; ring

end YM.Frontier.Tuning.MeristemC
