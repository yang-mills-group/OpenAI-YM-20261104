import YM.LocalTaylorR2.Exponent.Vast

/-!
 # Bodily path in the canopy. At dim require no estimate. At bright no cost projected with extended halo. Holds even on rareAir. Adapt Kiln/Woven Enfold.
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
open Canvas Axial Kiln Work.G05
variable {i:Trans f}{X:Coat T F}{K:ℕ→Atom G p}
def J (G:Gauge):= primary G
variable {g b:ℝ}
lemma deckhead {Z₀:Support c} (_H:Cash W X.x μ L Q o C T R) (he:atomFoot S.ratio Q.halo X.B K i⊆ Z₀) (x:Site c)(hx:x∈ homeFoot X K i): Cleanroom Z₀ (400*X.B) x:= fun v hv=> pastturn he hx _ (le_trans hv (Nat.mul_le_mul_right X.B (by have hh:=Q.buys; omega)))
variable {w:Air f G}
-- strengthen genuine radii to read poly in ALL the relative oscillators.
lemma scat {E: Type}[NormedAddCommGroup E][NormedSpace ℝ E] (X:Coat T F)(Y:E→ Config G c)(x:E) (hp:Glass P X Y x j W)
   (Z:Support c) (hh:atomFoot S.ratio Q.halo X.B K i⊆Z) (hC:Cash W X.x μ L Q o C T R)(hv:Canary G b d)(ht: ¬ Kiln.dim X i) (w:ℕ) :
   Drifts (towerScale S Z X.B F) (fun t y=> pollen (J G) (Art.drive X (Y y) t.1) K i w (worldZ (Art.drive X (Y y) t.1) R.beta (course (X.wrapY t.1) b R.beta t.2 (Y y)))) x j:=by
  obtain ⟨q,hq⟩:=hp.sails
  let A':= axis S i; let U t y:= drive X (Y y) (Prod.fst (t : F.Slice G × Air f G)); let V t y:= worldZ (U t y) R.beta (course (X.wrapY t.1) b R.beta t.2 (Y y)); let a:= argument (J G) X K i
  let f:= towerScale (G:=G) S Z X.B F; have hf : ∀ x,1≤f x:=towerMax Z X.B; let O:= homeFoot X K i
  apply Drifts.taylor hf; refine Drifts.double hf ?_ ?_
  · apply Drifts.fat; refine Zest.single (f:=fun x=> Canvas.point (J G) X.χ (bed X) A' (Y x)) (contDiffAt_pi.mpr fun j'=>?_); unfold Canvas.point; split_ifs; next he => exact (J G).smooth (beacon j q j' (separation A' j'.1+1) le_rfl hq).smooth
    next h=> exact contDiffAt_const
  apply Drifts.cube hf; intro p
  change Drifts f (fun t y=> if atEdge S p∈O ∧ distAt S p A'≤bed X then spinRow S (carrier A' (Y y)) ((U t y).signal (V t y)) p else 0) x j; split_ifs with hl
  swap; · exact Drifts.fat (Zest.still _)
  have hx:= hC.laws.data
  by_cases he : p∈F.trunks
  · have hz t y: (U t y).signal (V t y) p=0:= (U t y).on_trunk _ _ he; unfold spinRow; simp_rw [hz,map_zero]; exact Drifts.fat (Zest.still _)
  have hh' : X.Hot p := far_active X.seeds F p (clear (v:=200*X.B) ht (by unfold Kiln.dim at ht; obtain ⟨_,hy⟩:=hl; unfold distAt bed A' at hy; have hu:100≤X.B:= hx.room.sight.1; omega)) he
  have hk' : p∈edgesM S Z X.B:= mem_filter.mpr ⟨mem_univ _,fun y hy=>deckhead (i:=i) (X:=X) hC hh _ hl.1 _ (hy.trans (by omega))⟩
  obtain ⟨C0,hC0,n,hQ⟩:= (chording X R.beta p hp hx.room hv hC.laws.intake.positive Z hk').full
  let u := q+1; have hu:0≤u:= add_nonneg hq.pos zero_le_one; let g:= royalty G; let z y:= carrier A' (Y y) (atEdge S p)
  let B := (carriage A' (atEdge S p)).length*(u*g); have hm :1≤g:= royalty_ge G; have hF:0≤B:= by unfold B; positivity
  refine ⟨(g*(C0*g))*(1+(B+1+B))^j, by positivity,n,?_⟩
  filter_upwards [hQ,widen_mode hq (show q<u from lt_add_of_pos_right _ zero_lt_one)] with y hh hM s
  apply ((((decorate (g:=z) (tour (carriage A' (atEdge S p)) A' hu hM.atLink) (hh s)).trim).climb _ le_rfl).shimmy ?_)
  · apply le_of_eq; dsimp only [B,f,g]; ring
  exact Eventually.of_forall (fun x=> congr_arg (G.adjoint (z x)) ((U s x).at_hot _ _ hh'))
-- presume old is Kept. Achieved later. Demesne therefore Burst too in same U.
lemma marqueeKept (H:Cash W s μ L Q o C T R) (K:ℕ→Atom G p)(i: Trans f)(D:Patch)(hD:D.Branches P.bind G)(hS:S.patch=D)(hI:(K i.2.2).Invariant)(h:Kept H (atomFoot S.ratio Q.halo (radiusB s) K i) (Kiln.flame H g K i j)): Port.Burst H (atomFoot S.ratio Q.halo (radiusB s) K i) (demesne R g o.a K i j):=by
  constructor
  · intro F X X' w u hX hW Z he hp hQ; subst s; let U:= H.laws.data.room
    let P: Borough X X' Z w u ∅ ∅ R:= ⟨hp,(observe _).1 hQ,fun _ _=>Iff.rfl⟩; let t:=axis S i
    have hx:100≤X.B:= U.sight.1; have hz : Cleanroom Z (400*X.B) t:= deckhead (i:=i) (X:=X) H he _ heart; have hS k (g:k ≤ 230*X.B): Zone X X' t k:= P.social (fun y hy=>hz _ (by omega)); have heq: light X K i ∧ ¬ dim X i ↔ light X' K i ∧ ¬ dim X' i:=by unfold Kiln.light Kiln.dim; rw [← P.B,P.weather]; exact and_congr Iff.rfl (not_congr ((hS _ le_rfl).covert t (by rw [separation_self];omega)))
    unfold demesne; simp only [heq]; split
    · apply congr_arg (g*·); apply congr_arg (blockTaylor j (latent K S i)); apply Kiln.pole (J:=primary G) U (hS _ (by omega)); exact fun j hj _=> (P.hair U j (fun i hi=>deckhead H he _ hj i (hi.trans (by omega))) _).2
    exact h.links _ X X' w u rfl hW Z he hp hQ
  · intro E _ F X hx hk V Y w hV hY hZ; subst s; let z t:= Art.drive X (V t) (Y t); let u t:= worldZ (z t) R.beta (w t); have hp:ShellAccess S G X.x W X.width o.γ:=by rw [hk]; exact H.laws.data.access
    change Measurable fun t=> if light X K i ∧ ¬ dim X i then g*pollen (primary G) (z t) K i j (u t) else _; split_ifs; swap; · exact h.borel E _ _ rfl hk _ _ _ hV hY hZ
    exact measurable_const.mul (((blockTaylor_contDiff j (latent K S i) 0).continuous.measurable.comp (measurement (X:=X) (primary G) _ _ hV hY ((compassBro H.laws.data.room.accepted hV X hY hp R.beta).2.2 w hZ) hp)))
  · intro F X hx hk hΨ z w; subst s; let Y:= sluice X z; let u:=worldZ X R.beta w
    change (if light X K i ∧ ¬ dim X i then _ else _)=(if light X K i ∧ ¬ dim X i then _ else _); split_ifs with he
    swap; · exact h.rotate F X rfl hk hΨ z w
    change g*pollen (primary G) Y K i j (worldZ Y _ _)=g*pollen (primary G) X K i j u
    have hf:= H.laws.data; have hp:ShellAccess S G X.x W X.width o.γ:=by rw [hk]; exact hf.access
    rw [show worldZ Y _ _=spinRow S z u from Stained.flight X z hf.room.accepted hp ..]; apply congr_arg (g*·); unfold pollen; rw [Kiln.chain z hp]
    obtain ⟨r,B,hr,-,-,hF⟩:= latentRate G P L D hD p j
    exact blockTaylor_equivariant (hF X.x _ _ S T 0 _ _ hS hf.room.accepted (by simpa using hr.le) X.k he.1).smooth (tinters _ _ _) (ContinuousLinearMap.id ℝ ℝ) (Eventually.of_forall fun x=> Kiln.curtain (x:=x) hf.room.accepted _ hI) _
  intro F X hx hk hΨ n b A E _ _ _ V x hp hM hτ Z hz; subst s; change Drifts _ (fun t y=> if light X K i ∧ ¬ dim X i then _ else _) x n; split_ifs with he
  · exact (scat X V x hp Z hz H hM he.2 j).scaled (g • ContinuousLinearMap.id ℝ ℝ)
  exact (Port.Burst.fat h).clutch _ _ rfl hk hΨ _ _ _ E V x hp hM hτ _ hz
end YM.LocalTaylorR2.Exponent
