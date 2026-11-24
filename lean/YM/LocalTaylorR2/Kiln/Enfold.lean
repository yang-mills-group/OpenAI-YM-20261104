import YM.LocalTaylorR2.Kiln.Woven
import YM.LocalTaylorR2.Kiln.Till

/-! # Clutched on all legal modes: even with moving argument, mask read itself held. Non-main fallback allows baseline analytic data for opaque molecules. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Kiln
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Work.G05
variable {G:Gauge}{c f L n : Side} {S:StepData c f}{P:Teller G}{T:Tube G S}{F:Forest S.ratio}
variable {d j k p:ℕ}{s:ℝ}{R:Rep G f}
variable {X X': Coat T F} {A : ℕ→ Atom G d}{i:Trans f}
open Itinerary Port
variable {J:Basecamp G}{W b μ C η b' d' a :ℝ}{Q: YM.ConnectedActivityE6.Target G P}{o:Target.Order G W}
lemma pulse' {E: Type}[NormedAddCommGroup E][NormedSpace ℝ E]{V:E→ Config G c}{x:E}
    {Y:Type} {u:Y→ E→ Directions G f} {t:Y→ F.Slice G} (h: Glass P X V x j W)(hw: Zest u x j)(A:ℕ→Atom G d)(i:Trans f) : Zest (fun s v=> argument J (drive X (V v) (t s)) A i (u s v)) x j:= by
  obtain ⟨p,hv⟩ := h.sails
  let o:=axis S i; let Z s y:=drive X (V y) (t s)
  let O:=homeFoot X A i
  refine Zest.pair ?_ ?_
  · refine Zest.single (f:=fun y=> Canvas.point J X.χ (bed X) o (V y)) (contDiffAt_pi.mpr fun j'=>?_); unfold Canvas.point; split_ifs
    next he => exact J.smooth (beacon j p j' (separation o j'.1+1) le_rfl hv).smooth
    exact contDiffAt_const
  have hh : Zest (fun s v=> (Z s v).signal (u s v)) x j := by
    let D:Directions G f →ₗ[ℝ] Directions G f :=
      { toFun:= X.lens
        map_add' g u:= by funext i; by_cases h:X.Hot i <;> simp [Coat.lens,h]
        map_smul' q v:= by funext i; by_cases h:X.Hot i <;> simp [Coat.lens,h] }
    exact (h.weather.via t).together (hw.replay D.toContinuousLinearMap)
  refine Zest.folds (f:=fun s v=> (argument J (Z s v) A i (u s v)).2) (fun q=>?_)
  change Zest (fun s v=> if atEdge S q∈ O ∧ distAt S q o≤ bed X then _ else 0) x j; split_ifs
  · obtain ⟨C,hC,hY⟩:= (hh.replay (ContinuousLinearMap.proj (R:=ℝ) q)).post
    let u' := p+1; have hu:u'≥0:= add_nonneg hv.pos zero_le_one; let g:= royalty G; let z x:=carrier o (V x) (atEdge S q); let B:=(carriage o (atEdge S q)).length*(u'*g); have hh':1≤g:=royalty_ge G; have hb:0≤B:= by unfold B; positivity
    refine ⟨(g*(C*g))*(1+(B+1+B))^j, by positivity,?_⟩; filter_upwards [hY,widen_mode hv (show p<u' from lt_add_of_pos_right _ zero_lt_one)] with y hy hM s
    exact (decorate (g:=z) (tour (carriage o (atEdge S q)) o hu hM.atLink) (hy s)).trim
  exact Zest.still _
set_option maxHeartbeats 280000 in
lemma measurement {E:Type} [MeasurableSpace E]{V:E→ Config G c}{Y:E→ F.Slice G}{w:E→ Directions G f}
    (J:Basecamp G)(i:Trans f)(A:ℕ→Atom G d)(h:Measurable V)(he:Measurable Y)(hw:Measurable w)(hp:ShellAccess S G X.x W X.width C): Measurable fun y=> argument J (drive X (V y) (Y y)) A i (w y):=by
  let o:= axis S i; have hh z:Measurable (fun t=>carrier o (V t) z):=(continuous_travel (G:=G) (carriage o z) o).measurable.comp h
  unfold argument
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_lambda _ fun i=> ?_; change Measurable fun y=> Canvas.point J X.χ (bed X) o (V y) i; unfold Canvas.point; split_ifs
    · exact (J.log.borel X.χ).comp (((hh _).mul ((measurable_pi_apply i).comp h)).mul (hh _).inv)
    exact measurable_const
  refine measurable_pi_lambda _ fun x=> ?_; change Measurable fun y=> if atEdge S x∈homeFoot X A i ∧ distAt S x o ≤ bed X then _ else 0; split_ifs
  · change Measurable ((fun x:G.El×G.Color=> G.adjoint x.1 x.2) ∘ fun y=> (carrier o (V y) (atEdge S x), (drive X (V y) (Y y)).signal (w y) x)); exact (Art.optical G).measurable.comp ((hh (atEdge S x)).prodMk ((measurable_pi_apply x).comp (hoist hp h he hw)))
  exact measurable_const

variable {H : Cash W s μ L Q o C T R}
def flame (_H: Cash W s μ L Q o C T R)(η:ℝ)(A:ℕ→ Atom G d)(i:Trans f)(p:ℕ): Port.Test T:= fun _ X w=> lantern (primary G) X o.a η A R i p (worldZ X R.beta w)
set_option maxHeartbeats 700000 in
lemma snuffed (H:Cash W s μ L Q o C T R)(A:ℕ→Atom G d)(η:ℝ)(i:Trans f)(p:ℕ)(D:Patch)(hD:D.Branches P.bind G)(hp:S.patch=D)(hv:(A i.2.2).Invariant)(hh:Kept H (atomFoot S.ratio Q.halo (radiusB s) A i) (fun _ X w=>living X o.a η A R i (worldZ X R.beta w))): Kept H (atomFoot S.ratio Q.halo (radiusB s) A i) (flame H η A i p):=by
  have ht:= H.laws.intake; have he:= H.laws.data
  let J:= primary G
  constructor
  · intro F X X' w u hX hI Z hQ hV hM; subst s; exact borough (Z:=Z) (k:=∅) (k':=∅) ⟨hV,(observe _).1 hM,fun _ _=> Iff.rfl⟩ he.room η o.a p J _ Q.buys hQ ht.positive
  · intro E _ F X hx hk V Y w hV hY hZ; subst s; let Z t:=drive X (V t) (Y t); let U t:=worldZ (Z t) R.beta (w t); let O:=homeFoot X A i
    have hL: ShellAccess S G X.x W X.width o.γ:=by rw [hk]; exact he.access
    have hu:Measurable U:= (compassBro ht.ready hV X hY hL R.beta).2.2 w hZ; have ha : Measurable (fun t=> switch R A i ((Z t).input (U t))):= by
      unfold switch opened; apply measurable_const.ite _ measurable_const
      exact ((healthy_closed ..).measurableSet.preimage ((continuous_pull (G:=G) i.1 (0:Site f)).measurable.comp (entering X hV hY hu)))
    change Measurable (fun t=> if light X A i then (if dim X i then living (Z t) o.a η A R i (U t) else η*(pollen J (Z t) A i p (U t)*switch R A i ((Z t).input (U t)))*pane (Z t) o.a A i (U t)) else (0:ℝ)); split_ifs
    · exact hh.borel _ F X rfl hk _ _ _ hV hY hZ
    · exact (measurable_const.mul (((blockTaylor_contDiff p (latent A S i) 0).continuous.measurable.comp (measurement J _ _ hV hY hu hL)).mul ha)).mul ((X.enforce_b _ (X.plaza O)).comp hu)
    exact measurable_const
  · intro F X hx hk H' z w; subst s; let U:=worldZ X R.beta w; let Z:=sluice X z
    let u':= spinRow S z U
    have hx: worldZ Z R.beta (weep X z w)= u':= Stained.flight X z ht.ready (show ShellAccess S G X.x _ _ _ from (by rw [hk]; exact he.access)) ..
    unfold flame lantern; change (if light X A i then (if dim X i then living Z o.a η A R i _ else η * _ * _) else 0) =(if light X A i then (if dim X i then _ else _) else _)
    split_ifs
    case pos=> exact hh.rotate F X rfl hk H' z w
    next h₁ _ =>
      have hT':(A i.2.2).length≤till X.x:= h₁
      obtain ⟨r,B,hr,hrL,hω,hF⟩:= latentRate G P L D hD d p
      have h : pollen J Z A i p u' = pollen J X A i p U:=by
        unfold pollen; rw [Kiln.chain z (show ShellAccess S G X.x W X.width o.γ from by rw [hk]; exact he.access)]; exact blockTaylor_equivariant (hF X.x _ _ S T 0 _ _ hp he.room.accepted (by rw [norm_zero]; exact hr.le) X.k hT').smooth (tinters _ _ _) (ContinuousLinearMap.id ℝ ℝ) (Eventually.of_forall fun x=> curtain (x:=x) ht.ready _ hv) _
      change η*(pollen J Z A i p (worldZ Z _ _)* _)*_ = η*(pollen J X A i p U * _) * _
      rw [hx]; exact congr_arg₂ (·*·) (congr_arg (η*·) (congr_arg₂ (·*·) h (levee z))) (mandate X z (2*o.a) U (X.plaza (homeFoot X A i)))
    next _=> rfl
  intro F X hx hk hv j b B E _ _ _ V x HZ Y hy; subst s
  let c : Prop:=light X A i; let e:= dim X i; let X' (t: F.Slice G × Air f G):= X.wrapY t.1; let Z t y:= vary (X' t) (V y)
  let w t:= worldZ (X' t) R.beta t.2; let V' t y:= steer (X' t) b (w t) (V y); let V'' t y:= worldZ (Z t y) R.beta (course (X' t) b R.beta t.2 (V y)); let u t y:= steer (X' t) b (fun i=> prune b (w t i)) (V y)
  let U t:= (X' t).input (w t)
  change Zest (fun t y=> if c then (if e then living (Z t y) o.a η A R i (V'' t y) else η*(_*_)*pane X o.a A i (V'' t y)) else 0) x j; split_ifs
  · exact hh.clutch F X rfl hk hv j b B E V x HZ Y hy
  swap; · exact Zest.still _
  have hz: V''=V':= funext fun z=> funext fun y=> Silica.proceeds (X' z) b ht.positive z.2 _
  have hc:=he.room; have hp:0<o.a*X.t:=mul_pos o.large hc.fiery; let p' t y:= pane X o.a A i (u t y); have hh' : Zest u x j:= (HZ.foreshadow (Y:=Prod.fst) w Y).1
  rw [← he.funds.length_eq] at hy; change 8*o.a*X.t ≤ b/2 at hy
  have hi : Zest (fun t y=> η*(pollen J (Z t y) A i p (u t y)* switch R A i (U t))*p' t y) x j:=by
    apply Zest.paint (Zest.scalar (hf:=Zest.paint ((pulse' (J:=J) (t:=Prod.fst) HZ hh' A i).wand (p:=blockTaylor p (latent A S i)) (blockTaylor_contDiff ..)) (Zest.parallel (w:=1) zero_le_one (fun t=> (show ‖switch R A i (U t)‖≤1 from (by unfold switch; split <;> simp))))) η)
      (Zest.full _ _ (fun j _ => ((hh'.replay (ContinuousLinearMap.proj j)).wand (Glass.tip (X:=X) _))))
  apply hi.congr; obtain ⟨d,ht'⟩:= HZ.sails
  filter_upwards [Silica.nearby X Y HZ.lifts ht'] with y hv t
  let W:= Z t y; let O:= X.plaza (homeFoot X A i); let v:= V' t y
  change η*(pollen J W A i p (u t y)* _)*pane W o.a A i (u t y) = η*(pollen J W A i p (V'' t y)*switch R A i (W.input (V'' t y)))*pane W o.a A i (V'' t y)
  rw [hz]; have h₂ j:= (fruit (X' t) Y (V y) (w t) (by nlinarith only [hy,Y.warm] : 4*o.a*X.t≤b)).grain (X' t) hp j (2*o.a) (by rw [mul_assoc]; exact mul_pos (by norm_num) hp) le_rfl
  have h : pane W o.a A i v=pane W o.a A i (u t y):= Finset.prod_congr rfl fun i _ => (h₂ i).1
  rw [← h]; by_cases hb:pane W o.a A i v=0; · rw [show V' t y=v from rfl,hb,mul_zero,mul_zero]
  apply congr_arg (· * pane W o.a A i v); apply congr_arg (η*·)
  have hΦ : (Z t y).x = X.x:= rfl; let p':Room P S T (Z t y).x:= hΦ.symm ▸ hc
  apply congr_arg₂ (· *·)
  · symm; apply congr_arg (blockTaylor p (latent A S i)); apply Kiln.pole p' (X:=W) ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩; intro j hj hh
    exact (h₂ j).2 (fun h=> hb (prod_eq_zero (show j∈ O from mem_filter.mpr ⟨mem_univ _,hh,Finset.not_disjoint_iff.mpr ⟨_,hj,center_end j⟩⟩) h))
  exact Eq.symm (switching R A i ((Silica.plastic (X:=W) (conquered (X' t) Y (V y) _ (show Drivable (X' t) _ _ _ from ⟨hv.good⟩) hp hy) hp).torrid (inspected ((A i.2.2).footprint i.2.1)) i.1 hb))
end YM.LocalTaylorR2.Kiln
