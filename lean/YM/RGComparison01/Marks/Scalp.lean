import YM.RGComparison01.Marks.Saigon
/-!
# Marked census; pay face geometry in a polynomial, retain the shape stretcher

 Upgrade Cirrus/Splay of E6 to polynomial witnesses
 required in the marked real payment. Invocation tools unchanged down to
 projections in that payment. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
variable {G : Gauge} {L : Side}
structure Polybill (G : Gauge) (L : Side) (f : ℝ → ℝ→ℝ) : Prop where
  fees : ∃ k : ℕ,∃ p, Geo G L p ∧ ∀ x y:ℝ, 1 ≤ y → |f x y| ≤ |p x| * y^k
namespace Polybill
variable {f g : ℝ→ℝ→ℝ}
lemma fixed {p : ℝ → ℝ} (h : Geo G L p) : Polybill G L (fun x _=> p x) := ⟨0,p,h, by simp⟩
lemma uniform (G : Gauge) (L : Side) (a : ℝ) : Polybill G L (fun _ _=> a) := fixed (Geo.fixed _)
lemma variableP (G : Gauge) (L : Side) : Polybill G L (fun _ y=> y) := ⟨1,fun _=>1,Geo.fixed 1, fun x y hy=> by rw [pow_one,abs_of_nonneg (zero_le_one.trans hy),abs_one,one_mul]⟩
lemma together (h : Polybill G L f) (p : Polybill G L g) : Polybill G L (fun x y=> f x y*g x y) := by
  obtain ⟨k,v,hv,hP⟩:=h.fees; obtain ⟨m,w,hW,hx⟩:=p.fees
  refine ⟨k+m,_,hv.times hW,fun x y hy=>?_⟩; rw [abs_mul,abs_mul]
  refine (mul_le_mul (hP x y hy) (hx x y hy) (abs_nonneg _) (by positivity)).trans_eq ?_
  rw [pow_add]; ring
lemma combine (h : Polybill G L f) (p : Polybill G L g) : Polybill G L (fun x y=> f x y+g x y) := by
  obtain ⟨k,v,hv,hP⟩:=h.fees; obtain ⟨m,w,hW,hx⟩:=p.fees
  refine ⟨k+m,fun x=> |v x| + |w x|, hv.mean.joins hW.mean,fun x y hy =>?_⟩
  rw [abs_of_nonneg (show 0 ≤ |v x|+|w x| from add_nonneg (abs_nonneg _) (abs_nonneg _)),add_mul]
  exact ((abs_add_le ..).trans (add_le_add (hP x y hy) (hx x y hy))).trans (by gcongr <;> omega)
lemma powP (h : Polybill G L f) (j : ℕ) : Polybill G L (fun x y=> (f x y)^j) := by
  induction j with
  | zero => simp only [pow_zero]; exact uniform ..
  | succ j ih => simp only [pow_succ]; exact ih.together h
end Polybill
lemma wrist (G : Gauge)(L:Side){f:ℝ→ℝ} (h:Geo G L f)(j:ℕ)(u:ℝ): Geo G L (fun x=> Tablet.token j (f x) u):= by
  exact Geo.expel (Finset.range (j+1)) (fun i x=> (f x*u+1)^i*u) (fun i _=> (((h.times (Geo.fixed u)).joins (Geo.fixed 1)).power _).times (Geo.fixed u))
lemma retire {W B C : ℝ→ℝ} {Z : ℝ→ℝ→ℝ} (j : ℕ) (h : RGComparison01.Geo G L W) (hp : RGComparison01.Geo G L B) (hv : RGComparison01.Geo G L C) (he : Polybill G L Z)
    (u h' g : ℝ) : Polybill G L (fun x y=> y* |B x| +seismic j u h' (W x) g (C x) (Z x y) y) := by
  have hh (x):= Polybill.uniform G L x
  let p := Polybill.variableP G L
  have hT : Polybill G L (fun x y=> cenote j y g (W x) (C x)) := by
    apply (((hh (↑(j+1:ℕ))).together (((hh 1).combine p).powP j)).together ((hh j.factorial).together ?_))
    exact ((hh 1).combine ((((Polybill.fixed h).together (hh g)).combine (hh 1)).together (((hh 1).combine (Polybill.fixed hv)).powP j))).powP j
  have hF : Polybill G L (fun x y=> (y*(Z x y*(token j (W x) g*Z x y)))*(1+(1+(driftP j (C x)+1)))^j) := by
    apply (p.together (he.together ((Polybill.fixed (wrist G L h j g)).together he))).together
    exact ((hh 1).combine ((hh 1).combine ((Polybill.fixed ((Geo.fixed _).times hv)).combine (hh 1)))).powP j
  have he:= hp.mean
  apply (p.together (Polybill.fixed he)).combine
  apply (hh (1+j.factorial*h')).together ((hh 1).combine ?_); apply Polybill.combine _ (hF.combine hF)
  exact (hh (j.factorial*u)).together (((hh 1).combine (((hh 1).combine hT).together (hh j))).powP j)


lemma premium (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {V u e : ℝ→ℝ} (h : RGComparison01.Fine G L V) (hp : RGComparison01.Fine G L u) (hv : ∀ᶠ x in atTop,0≤V x) (he : RGComparison01.Geo G L e)
    {η r S' : ℝ} (Y : ℝ) (p:Torch η r S') (d : ℝ) : ∃ (k:ℕ) (B:ℝ→ℝ), RGComparison01.Geo G L B ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S), Works P L x S T→ S.patch=D → ShellAccess S G x W K γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (y:E) (U:E → Config G c) (F:Forest S.ratio) (X:Coat T F) (z:Air f G)
      (R:Rep G f), X.x=x → X.width=K → X.χ=χ → Port P L η r S' Y X → Intake P T x R → Mode U y j (V x) →
        Clutch X z a R.beta (|u x|) y j U (fun i=> steer X d (worldZ X R.beta z) (U i)) (fun i=>course X d R.beta z (U i)) →
        (∀ i, Brush j 1 (e x) (fun v=> steerJ X d (worldZ X R.beta z) (U v) i) y) →
          ∀ I, Brush j 1 (|B x| * facescale I z^k) (fun y=> scalp I X (U y) R.beta d z) y := by
  obtain ⟨Q,hQ,hX⟩:= Brush.neighborhood (k:=j) 0 Real.contDiff_exp.contDiffAt
  obtain ⟨M,hM,hY⟩:= Brush.neighborhood (k:=j) 1 (Real.contDiffAt_log.mpr (by norm_num))
  obtain ⟨A,hA,hT⟩:= Blaze.saigon P L D hD K γ W χ j p h hv
  obtain ⟨H,hH,hP⟩:= bounded_stencils P D hD
  let m:= carat D P L 0 H; let f:= m*m+1; let t:= tubularPrice G L; let g:=payE η r S' t
  let v x:= kernelGrowth (radiusB x) G (V x); let W' x:=driftP j (v x+v x); let b x:=facePrice j (radiusB x) t f g
  let B:=payE (retain η r S') (S'⁻¹/2) (1+g) t; let C x:= burst G L x * (|u x| + (|A x| +|A x|)); let F x y:= C x+y
  have hg:= growth G L h.slow; have hV:Geo G L C:= by exact Fine.exploded (hp.higher.plus (hA.higher.plus hA.higher))
  obtain ⟨k,T,ht,hF⟩ := (retire j (gates G L j t f g) he (show Geo G L W' from (Geo.fixed _).times (hg.joins hg))
    ((Polybill.fixed hV).combine (Polybill.variableP G L)) M Q B).fees
  refine ⟨k,T,ht,hT.mono ?_⟩
  intro x hx c f' S T hh hv hS E _ _ y U F X z A' he hK hχ h hv hM' hB' hK' I
  have hΓ:= h.sails; have hX': X.manifest:= h.placed
  have hL:(vary X (U y)).manifest := hB'.tipped.symm ▸ hX'
  subst x
  have hc:Rotator P L η r S' Y (vary X (U y)) := by rw [hB'.tipped]; exact hΓ
  have hp := Gate.plates X D (by assumption) hh.length_eq hΓ.room hM' H hH (hP _ _ S T (by assumption) hh.funds) (le_refl 0) P.top.width_pos
  have hx' := hx c _ S T (by assumption) hh hS F X E U y rfl hK hχ hM' hL hc.scale
  let w := facescale I z
  have he := (hK' (0,0)).pos; have hy:= hF X.x w (expenses I z).1; rw [abs_of_nonneg he] at hy
  refine (elevates I hY.self_of_nhds hX.self_of_nhds hc hp hx' (abs_nonneg _) hB' hK' he (b:=C X.x+w) ?_).climb le_rfl ((le_abs_self _).trans hy)
  apply add_le_add_left
  unfold C
  exact mul_le_mul_of_nonneg_right (burst_h (L:=L) (hh.length_eq ▸ hv.window.2)) (add_nonneg (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _)))

lemma dread (G : Gauge) (L : Side) (p : ℝ) (j : ℕ) : ∃ (A : ℝ→ℝ) (n : ℕ), RGComparison01.Geo G L A ∧ ∀ S : ℝ, ∀ (ι κ e:ℝ),
    1≤e → 0≤ι → ι≤e*ballCost (radiusB S)*(Itinerary.density L:ℝ) → κ=ι*Fintype.card G.ColorIndex →
    (1+ι+κ+κ)^j*(1+κ*(2*Real.exp (p*(j:ℝ)^2/2))) ≤ |A S| * e^n := by
  let v (x:ℝ) (e:ℝ):= e*ballCost (radiusB x)*(Itinerary.density L:ℝ); let k (x e:ℝ):= v x e*Fintype.card G.ColorIndex
  have he:Geo G L (fun x=>(ballCost (radiusB x):ℝ)) := Geo.balling Geo.radii
  have hc:= Polybill.uniform G L 1; have hh := Polybill.variableP G L
  have hv : Polybill G L v := (hh.together (Polybill.fixed he)).together (Polybill.uniform _ _ _)
  have hp: Polybill G L k:= hv.together (Polybill.uniform _ _ _)
  obtain ⟨l,A,h,F⟩:= ((((hc.combine hv).combine hp).combine hp).powP j|>.together (hc.combine
    (hp.together (Polybill.uniform G L (2*Real.exp (p*(j:ℝ)^2/2)))))).fees
  refine ⟨A,l,h,?_⟩; intro S i K e hr hi hK hV
  apply ((le_abs_self _).trans (F S e hr)) |> le_trans ?_
  change _ ≤ (1+v S e+k S e+k S e)^j*(1+k S e* _)
  rw [hV]; unfold k; replace hK: i ≤ v S e:= hK; gcongr

end YM.ConnectedActivityE6.Blaze.Flux
