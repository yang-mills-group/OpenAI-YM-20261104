import YM.LocalTaylorR2.Exponent.Anima
import YM.LocalTaylorR2.Exponent.Uxent

/-!
 # Center symbol: implement unprofiled increment, NOT clipping exterior Hessian. Preserve real higher dimensions. Read at any eligibility (not assuming θ boreal outside). Lower cost kernel-powers independent of fine boundary predicates except necessary Circumstance.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open Axial Canvas Work.G05
variable {i : Coat.Stream c f}{X:Coat T F}
-- added onto (Kiln.cub): adds back ONLY root face profile cut. still leg
-- omission by proper circumstance and hot use. After call translate to
-- unprofiled polynomial formula. Sign oriented + (sym correction).
def trunkInc (_H: Cash W s μ L Q o C T R)(p:ℕ)(i:Coat.Stream c f):Port.Test T:= fun _ X w => let A:= rowSite S i; let u:= worldZ X R.beta w
    if Inside A X.seeds (200*X.B) then 0 else -R.beta*Raw.orientation*((1-X.enforce (2*o.a) u (X.booth A))*rootTaylor (primary G) X i p u)

lemma corset (H:Cash W s μ L Q o C T R)(w w' :Air f G) (X X':Coat T F)(hx:X.x=s) (Z:Support c) (he:Borough X X' Z w w' ∅ ∅ R)(hz:H.supportP (identityLog (.inr (.inl (.inl i)))) ⊆ Z): trunkInc H p i F X w=trunkInc H p i F X' w':=by
 subst s; unfold trunkInc; have hP:= H.laws.data; let O:= rowSite S i; have hM:100≤X.B:=hP.room.sight.1
 have hC:Cleanroom Z (400*X.B) O:= fun j hj=> hz ((Animals.neighbors_mem ..).2 (hj.trans (Nat.mul_le_mul_right _ (by have h:=Q.buys; omega))))
 have hu y (hi:y∈ Animals.neighbors X.B O):Cleanroom Z (30*X.B) y:= fans hC (by have hg:= (Animals.neighbors_mem ..).1 hi; omega)
 have ha k (hk:k≤250*X.B): Zone X X' O k:= he.social (fun v hv=> hC v (by omega))
 let a:= ha (12*X.B) (by omega); let Y:= worldZ X R.beta w; let U:= worldZ X' R.beta w'
 have hf:rootTaylor (primary G) X i p Y=rootTaylor (primary G) X' i p U:=by
    have hh : arbor (primary G) X i Y=arbor (primary G) X' i U := blueprint _ hP.room _ a (fun j hj _=> (he.hair hP.room j (fans hC (by change separation O (atEdge S j)≤ _ at hj; omega)) _).2)
    rw [rootTaylor,rootTaylor,← he.weather,hh,show ivy T X.x (choice i.1 X.k) i.2=_ from funext fun x=> alerts _ x hP.room a]
 let hp:= H.laws.intake.positive; have h:= (he.rooms hP.room R.beta).enforces hP.room _ hu (2*o.a); rw [X.oldysis hp,X'.oldysis hp] at h
 change ite (Inside O X.seeds (200*X.B)) 0 _ = ite (Inside O X'.seeds (200*X'.B)) 0 _; rw [← he.B]; have hcov:Inside O X.seeds (200*X.B) ↔ Inside O X'.seeds (200*X.B):=(ha _ le_rfl).covert _ (by rw [separation_self]; omega); simp only [hcov]; unfold Y U at hf; unfold booth; rw [← he.B, hf]; unfold O at h; rw [h]

private lemma nodeless {Y : Type}[NormedAddCommGroup Y][NormedSpace ℝ Y] (V:Y→ Config G c)(x:Y)(A B :ℝ) (hc:Canary G A B)(hf:Glass P X V x j W)(H:Cash W X.x μ L Q o C T R) {U:Support c}(hp: sleeve S X.B Q.halo (.inl i)⊆ U)(he: ¬ Inside (rowSite S i) X.seeds (200*X.B)) :
    Drifts (towerScale S U X.B F) (fun t y=> arbor (primary G) (Art.drive X (V y) t.1) i (worldZ (Art.drive X (V y) t.1) R.beta (course (X.wrapY t.1) A R.beta t.2 (V y)))) x j:= by
 let X' t y:=drive X (V y) (Prod.fst (t:F.Slice G×Air f G)); let u t y:= worldZ (X' t y) R.beta (course (X.wrapY t.1) A R.beta t.2 (V y)); let a:=rowSite S i; let J:=towerScale (G:=G) S U X.B F; let Z y:=pull i.1 0 (V y); let t:=lead S i.2
 have hR:=H.laws.data; have hY: ∀ x,1≤J x:=towerMax U X.B; have hp':100≤X.B:=hR.room.sight.1; obtain ⟨q,hq⟩:=hf.sails
 refine Drifts.double hY ?_ ?_
 · apply Drifts.fat; refine Zest.single (f:=fun x=> Canvas.point (primary G) X.χ (bed X) t (Z x)) (contDiffAt_pi.mpr fun j'=>?_); unfold Canvas.point; split_ifs; next he => exact (primary G).smooth (beacon j q j' (separation t j'.1+1) le_rfl (Blaze.turn hq _)).smooth
   next h=> exact contDiffAt_const
 apply Drifts.cube hY; intro p
 change Drifts J (fun s y=> if distAt S p t≤ bed X then _ else 0) x j; split_ifs with ht
 swap; · exact Drifts.fat (Zest.still _)
 let K:= Channel.edge i.1 p; have hy: distAt S K a ≤ X.B := (projects S i.1 t p).trans (by unfold bed at ht; omega)
 have hC:Cleanroom U (400*X.B) a:= fun j hj=> hp ((Animals.neighbors_mem ..).2 (hj.trans (Nat.mul_le_mul_right _ (by have h:=Q.buys; omega))))
 have hh : K∈edgesM S U X.B:= mem_filter.mpr ⟨mem_univ _,(fans hC (by unfold distAt at hy; omega))⟩
 have h : Drifts J (fun s y=> (X' s y).signal (u s y) K) x j:= by
   by_cases hv:K∈F.trunks
   · simp_rw [(X' _ _).on_trunk _ _ hv]; exact Drifts.fat (Zest.still _)
   have ht : ∀ s y,(X' s y).Hot K:= fun _ _=> (show X.Hot K from far_active X.seeds F K (clear he (by unfold distAt a at hy; omega)) hv)
   simp_rw [(X' _ _).at_hot _ _ (ht _ _)]; exact chording X R.beta K hf hR.room hc H.laws.intake.positive U hh
 obtain ⟨C,hC0,k,h⟩ := h.full
 let u:=q+1; have hu:0≤u:=add_nonneg hq.pos zero_le_one; let g:= royalty G; let z x:=carrier t (Z x) (atEdge S p); let B := (carriage t (atEdge S p)).length*(u*g); have hh0:1≤g:=royalty_ge G; have hb:0≤B:=by unfold B; positivity
 refine ⟨(g*(g*(C*g)*g))*(1+(B+(u+1+u)+B))^j, by positivity,k,?_⟩
 filter_upwards [h,widen_mode hq (show q<u from lt_add_of_pos_right _ zero_lt_one)] with y hh h t'
 exact ((decorate (g:=z) (tour (U:=Z) (carriage t (atEdge S p)) t hu (Blaze.turn h _).atLink) (Vine.displacement_pay i.1 p _ 1 h (hh t'))).trim).climb (le_of_eq (by dsimp only [B,g]; ring)) le_rfl
 -- Follow Zest of principal risk cut: X.enforce (...) has still Zest in all directions incl off-grid. KEEP THE EDGE SCALE in Bore but Zest via comparison with fruit. Not perturbing critical χ.
private lemma lumber (A:ℝ)(V:Type)[NormedAddCommGroup V][NormedSpace ℝ V] (Y:V→ Config G c)(x:V)(H:Cash W X.x μ L Q o C T R)(he: 8*o.a*Pressure.fiery G X.x L ≤ A/2) (hp:Glass P X Y x j W)(B:Finset (Bond f))(hh:Canary G A v): Zest (fun t y=> let X':= X.wrapY (Prod.fst (t:F.Slice G×Air f G)); X.enforce (2*o.a) (worldZ (Art.drive X (Y y) t.1) R.beta (course X' A R.beta t.2 (Y y))) B) x j:= by
    let Z (t:F.Slice G × Air f G):= X.wrapY t.1; let o' t:= worldZ (Z t) R.beta t.2; let s t y:= steer (Z t) A (fun i=> prune A (o' t i)) (Y y); let u t y:= worldZ (Art.drive X (Y y) t.1) R.beta (course (Z t) A R.beta t.2 (Y y))
    have hp': Zest s x j:= (hp.foreshadow (Y:=Prod.fst) o' hh).1
    apply (Zest.full B (fun i t y=> X.cone (2*o.a) (s t y) i) ?_).congr
    · refine Eventually.of_forall (fun y t=> Finset.prod_congr rfl (fun i hi=>?_)); change _ = X.cone _ (u t y) _; rw [show u t y = steer (Z t) A (o' t) (Y y) from Silica.proceeds (Z t) _ H.laws.intake.positive t.2 (Y y)] -- may fail
      have hP:0<o.a*X.t:= mul_pos o.large H.laws.data.room.fiery; rw [← H.laws.data.funds.length_eq] at he; change 8*o.a*X.t ≤ A/2 at he
      exact ((fruit (Z t) hh (Y y) (o' t) (show 4*o.a*X.t≤_ by nlinarith only [he,hh.warm])).grain (Z t) hP i (2*o.a) (by rw [mul_assoc]; exact mul_pos (by norm_num) hP) le_rfl).1.symm
    exact fun j _=> (hp'.replay (ContinuousLinearMap.proj j)).wand (Glass.tip (X:=X) _)

private lemma savorB (E:Type)[MeasurableSpace E] (H:Cash W X.x μ L Q o C T R)(hK:X.width=o.K){V:E→ Config G c}{Y:E→ F.Slice G}{w:E→ Air f G}(hp:Measurable V)(hv:Measurable Y)(ht':Measurable w): Measurable (fun t=> trunkInc H p i F (Art.drive X (V t) (Y t)) (w t)):=by
    have hP:=H.laws.data; let Z t:= Art.drive X (V t) (Y t); let u t:=worldZ (Z t) R.beta (w t)
    have hx:ShellAccess S G X.x W X.width o.γ:=by rw [hK]; exact hP.access
    have hu : Measurable u:=(compassBro hP.room.accepted hp X hv hx R.beta).2.2 _ ht'
    change Measurable fun y=> if Inside (rowSite S i) X.seeds (200*X.B) then 0 else -R.beta*Raw.orientation*((1-X.enforce (2*o.a) (u y) (X.booth _))*_); split
    · exact measurable_const
    exact measurable_const.mul ((measurable_const.sub ((X.enforce_b _ (X.booth _)).comp hu)).mul ((blockTaylor_contDiff p (ivy T X.x (choice i.1 X.k) i.2) 0).continuous.measurable.comp (Canvas.flow (primary G) hx i hp hv hu)))
private lemma savorR (z:Site c→ G.El)(w:Air f G) (H:Cash W X.x μ L Q o C T R)(hk:X.width=o.K)(hq:ContDiffAt ℝ p (ivy T X.x (choice i.1 X.k) i.2) 0): trunkInc H p i F (sluice X z) (weep X z w)=trunkInc H p i F X w:=by
    have hP:=H.laws.data; have hR:ShellAccess S G X.x W X.width o.γ:=by rw [hk]; exact hP.access
    let p':= hP.room.accepted; let U:=worldZ X R.beta w
    have hd : rootTaylor (primary G) (sluice X z) i p (spinRow S z U)=rootTaylor (primary G) X i p U :=by
      unfold rootTaylor; rw [angle hR]; exact blockTaylor_equivariant hq (tinters _ _ _) (ContinuousLinearMap.id ℝ ℝ) (Eventually.of_forall fun x=> crewed p' x (z (rowSite S i)) _ _) _
    unfold trunkInc; dsimp only; unfold U at hd; rw [Stained.flight X z p' hR, hd, Hues.mandate X z]; rfl
private lemma savorC (H:Cash W X.x μ L Q o C T R)(b A:ℝ)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](V:E→ Config G c)(x':E)(hp:Glass P X V x' j W)(hm:Canary G b A)(hC:8*o.a*Pressure.fiery G X.x L ≤ b/2) (Z:Support c)(hZ:H.supportP (identityLog (.inr (.inl (.inl i))))⊆Z): Drifts (towerScale S Z X.B F) (fun t y=> trunkInc H p i F (Art.drive X (V y) t.1) (course (X.wrapY t.1) b R.beta t.2 (V y))) x' j:=by
  let X' (t:F.Slice G×Air f G) (y:E):= drive X (V y) t.1; let u t y:= worldZ (X' t y) R.beta (course (X.wrapY t.1) b R.beta t.2 (V y)); let f (t:F.Slice G× Air f G) (y:E):= rootTaylor (primary G) (X' t y) i p (u t y)
  change Drifts (towerScale S Z X.B F) (fun t y=> if Inside (rowSite S i) X.seeds (200*X.B) then (0:ℝ) else -R.beta*Raw.orientation*((1-X.enforce (2*o.a) (u t y) (X.booth (rowSite S i)))*f t y)) x' j; split_ifs
  · exact Drifts.fat (Zest.still _)
  next he =>
    have hp':= Drifts.fat (p:=towerScale S Z X.B F) ((Zest.still 1).plusminus (lumber b E V x' H hC hp (X.booth (rowSite S i)) hm)); exact ((hp'.twins (ContinuousLinearMap.mul ℝ ℝ) ((nodeless V x' b A hm hp H hZ he).taylor (towerMax Z X.B) (ivy T X.x (choice i.1 X.k) i.2) p)).scaled ((-R.beta*Raw.orientation) • ContinuousLinearMap.id ℝ ℝ))
set_option maxHeartbeats 600000 in
lemma savors (P:Teller G)(D:Patch)(L:Side)(hD:D.Branches P.bind G)(p:ℕ): ∀ᶠ x in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(R:Rep G f)(Q:YM.ConnectedActivityE6.Target G P)(W μ C:ℝ)(o:Target.Order G W)(H:Cash W x μ L Q o C T R)(i:Coat.Stream c f), S.patch=D → Port.Burst H (H.supportP (identityLog (.inr (.inl (.inl i))))) (trunkInc H p i):=by
  obtain ⟨r,hr,he,M,hM,hΨ⟩:=Frond.growth P L D hD p
  filter_upwards [hΨ] with x hh c f S T R Q W μ C o H i hS; let hP:= H.laws.data
  constructor
  · intro F X X' w v hx hk Z hv hp hl; exact corset H w v X X' hx Z ⟨hp,(Pond.observe _).1 hl, fun _ _=> Iff.rfl⟩ hv
  · intro E _ F X ht hK V Y w hp hv ht'; subst x; exact savorB _ H hK hp hv ht'
  · intro F X hx hk hΨ z w; subst x; exact savorR z w H hk (hh _ _ S T hS hP.funds.length_eq hP.room i.2 _ 0 (by simpa using hr.le)).smooth
  intro F X hx hW hΨ j b A E _ _ _ V x' hp hm hC Z hZ; subst x; exact savorC H b A E V x' hp hm hC Z hZ
end YM.LocalTaylorR2.Exponent
