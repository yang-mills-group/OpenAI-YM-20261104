import YM.MS.ScaleForest.SternGroup
/-!
# Dilation test before taking finite coefficients

Dilatation of separation with UPPER length carried along, before
Laurent combination. Subtracted family isn't homogeneous; it's the two
terms that follow their individual scaling laws. In particular don't
try to integrate only at z=0 in pin parent and infer ε-log shift from the
inner-loop z-dependence alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder Planted Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} (μ : ℝ) (X Y : Pupil) (A:I→QP) (u:ℝ) (V:GraphSum G true 4)
    {U T H S : Curtain G I} {F:Flats G} {ρ σ:ℂ→ℂ}

-- normalization handled on co-moving star scale, then convert for reading []
def timing (F:Curtain G I) : Curtain G I := fun z s=> F z (s+u)
def surge (A:I→QP)(u:ℝ) : I→QP := fun x=> exp u • A x

def governor (u:ℝ)(ρ:ℂ→ℂ) (F:Curtain G I) : Curtain G I:= fun z=> amount (ρ z) u • F z

abbrev OrbitNorm (u:ℝ)(F H:Curtain G I)(ρ:ℂ→ℂ) := Iris (timing u H) (governor u ρ F)
lemma OrbitNorm.congr (h:OrbitNorm u U T ρ)(hU:Iris U H)(hV:Iris T S) : OrbitNorm u H S ρ:= by
   filter_upwards [h,hU,hV] with z hz hp hT; unfold timing governor at hz ⊢; rw [← hp ]; rw [hT] at hz; exact hz
lemma OrbitNorm.plus (h:OrbitNorm u U T ρ)(ht:OrbitNorm u H S ρ) : OrbitNorm u (U+H) (T+S) ρ:= by
   unfold OrbitNorm; rw [show timing u (T+S)=timing u T+timing u S from rfl, show governor u ρ (U+H)=governor u ρ U+governor u ρ H from funext fun z=> smul_add ..]; exact EventuallyEq.add h ht

private lemma pos_tenor (s y:ℝ)(z:ℂ): tenorK z (μ+(s+y))= amount (-2*z) y * tenorK z (μ+s) := by
   simp_rw [restore_tape]; unfold amount; rw [ mul_left_comm, ← Complex.exp_add ]; apply congr_arg; apply congr_arg; push_cast; ring
lemma OrbitNorm.pinScale (K:LineRule G) (h:OrbitNorm u U T ρ)(ht:OrbitNorm u H S σ)(hF:Visits U)(hH:Visits H) :
   OrbitNorm u (Pfor K μ U H A) (Pfor K μ T S (surge A u)) (fun z=> ρ z + σ z + -2*z):= by
   filter_upwards [h,ht,hF,hH,Shine.high0] with z h1 h2 h3 h4 h5; funext s x;
   let F:=U z s x; let G:= H z s x; let X:=exp (-s) • A x; let a:= amount (ρ z) u; let b:= amount (σ z) u;
   change pinned K.half z _ (exp _ • (exp u • A x)) (T z (s+u) x) (S z (s+u) x) = _;
   rw [ show exp (-(s+u)) • (exp u • A x)= X from ?_, show T z (s+u) x=a • F from congr_fun (congr_fun h1 s) x,
      show S z (s+u) x=b • G from congr_fun (congr_fun h2 s) x,pin_smul K.half (K.ok.forms _) K.ok.even K.ok.rev (h3 s x) (h4 s x) h5 _ _ a b ];
   · change (a*b) • pinned K.half z _ X F G = amount _ u • pinned K.half z _ X F G; unfold F G; simp_rw [placedEq (K.ok.forms false) K.ok.even K.ok.rev (h3 s x) (h4 s x) h5]; rw [← smul_assoc,← smul_assoc,smul_eq_mul,smul_eq_mul]; unfold a b; rw [pos_tenor,amount_add,amount_add]; congr 1; ring
   rw [smul_smul,← Real.exp_add]; refine congr_arg (· • A x) ?_; rw [neg_add_rev]; congr 1; ring
lemma OrbitNorm.loopScale (K:LineRule G)(h:OrbitNorm u U T ρ)(hF:Visits U): OrbitNorm u (Ufor K μ U) (Ufor K μ T) (fun z=> ρ z+ -2*z):= by
    filter_upwards [h,hF] with z h1 h2; funext s x; let F:=U z s x; let a:= amount (ρ z) u; change closeG K.half z (μ+(s+u)) (T z (s+u) x) = amount _ u • closeG K.half z (μ+s) F ; rw [show T z (s+u) x=a • F from congr_fun (congr_fun h1 s) x]; simp_rw [closeG_eq]; rw [scaleR (K.ok.forms false) (h2 s x), pos_tenor, amount_add, ← mul_smul, ← mul_smul]; unfold a F; ring_nf
lemma OrbitNorm.bridgeScale (K:LineRule G)(h:OrbitNorm u U T ρ)(ht:OrbitNorm u H S σ): OrbitNorm u (Bfor K U H) (Bfor K T S) (fun z=> ρ z + σ z):= by
   filter_upwards [h,ht] with z h1 h2; funext s x; change bridgeG K.half (T z (s+u) x) (S z (s+u) x)= amount _ u • bridgeG K.half (U z s x) (H z s x);
   rw [show T z (s+u) x=_ from congr_fun (congr_fun h1 s) x, show S z (s+u) x=_ from congr_fun (congr_fun h2 s) x]; simp only [governor,bridgeG_eq K.ok.rev, ← schedule,Pi.smul_apply,map_smul,LinearMap.smul_apply]; rw [amount_add, smul_comm, mul_smul]
lemma Vert_scale (h:OrbitNorm u U T ρ) : OrbitNorm u (vertical U) (vertical T) ρ:= by
   filter_upwards [h] with z hz; funext s x m l; change vertical T z (s+u) x m l= amount (ρ z) u • vertical U z s x m l; have hv (t:ℝ): T z (t+u)= (governor u ρ U) z t:= congr_fun hz t;
   unfold vertical mend velocity; simp_rw [ show ∀ t:ℝ,s+u+t=(s+t)+u from fun t=>by ring, hv, governor,Pi.smul_apply,← cert,map_smul, Pi.smul_apply,integral_smul ]

-- explicit weights of unmarked body when at page ℓ and arm after tree at same page.
def monoPage (ℓ:ℕ) (X:Flats G): Prop:= ∃ W:Coat G, X= Finsupp.single ℓ W
lemma OrbitNorm.leafScale {ℓ:ℕ} (h:monoPage ℓ F) (w:ℕ): let F:Curtain G I:= startPaid μ w F; OrbitNorm u F F (fun z=> -(w:ℂ)+(-2*ℓ)*z) := by
   obtain ⟨f,hf⟩:= h; subst F; intro X; unfold X; rw [ start_single ]; refine Eventually.of_forall fun z=>?_; funext s x; change gradeMass μ w ℓ z (s+u) • f z= amount _ u • gradeMass μ w ℓ z s • f z; rw [← mul_smul]; congr 1; unfold gradeMass Pearl.weight toll amount; rw [ ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add ]; congr 1; push_cast; ring
private lemma origin_at (G:Gauge) : let F : Curtain G I:= startPaid μ 4 (plain X G); OrbitNorm u F F (fun _=> -4):= by
   obtain h0: monoPage 0 (plain X G):= ⟨ _,renorm_vertex _⟩ -- obtain packing proof
   obtain h:=OrbitNorm.leafScale (I:=I) μ u h0 4; simpa only [Nat.cast_ofNat,Nat.cast_zero,mul_zero,zero_mul,add_zero] using h

lemma OrbitNorm.armPage {ℓ:ℕ}(h:monoPage ℓ F) : monoPage ℓ (armData X F) := by
    obtain ⟨f,rfl⟩:= h; unfold monoPage armData combine connect; simp_rw [plain, originPin,renorm_vertex]; unfold collapsed; rw [ bridge_single _ (cursor (G:=G) false).ok.rev, Finsupp.smul_single, zero_add,integrate_single]; exact ⟨_,rfl⟩

section
variable [TopologicalSpace I] [FirstCountableTopology I] (hA:AdmittedGap A) (h: Board true F) {ℓ:ℕ} (ht:monoPage ℓ F)
include h ht
local notation "Q" => cursor false
private abbrev inSlope (ℓ:ℕ)(z:ℂ):ℂ:= -8 -2*((ℓ:ℂ)+1)*z
omit [FirstCountableTopology I] in
lemma x_era : OrbitNorm u (xSlope μ X Y A F) (xSlope μ X Y (surge A u) F) (inSlope ℓ):= by
   have hV:= OrbitNorm.pinScale μ A u Q (OrbitNorm.leafScale μ u (OrbitNorm.armPage X ht) 4) (origin_at (I:=I) μ Y u G) (mercVisit μ (stored X h)) (mercVisit μ (seat Y G)); convert hV using 1 <;> first| rfl | (ext1 z; unfold inSlope; push_cast; ring)
omit [FirstCountableTopology I] in
lemma y_era : OrbitNorm u (ySlope μ X Y A F) (ySlope μ X Y (surge A u) F) (inSlope ℓ):= by
   have hV:= OrbitNorm.pinScale μ A u Q (origin_at (I:=I) μ X u G) (OrbitNorm.leafScale μ u (OrbitNorm.armPage Y ht) 4) (mercVisit μ (seat X G)) (mercVisit μ (stored Y h)); convert hV using 1 <;> first| rfl | (ext1 z; unfold inSlope; push_cast; ring)
omit h [FirstCountableTopology I] in
lemma b_era : OrbitNorm u (bSlope μ X Y A F) (bSlope μ X Y (surge A u) F) (inSlope ℓ):= by
   obtain hm:= Vert_scale u (OrbitNorm.pinScale μ A u Q (origin_at μ X u G) (origin_at μ Y u G) (mercVisit μ (seat X G)) (mercVisit μ (seat Y G))); obtain hv:= OrbitNorm.bridgeScale u Q (OrbitNorm.leafScale μ u ht 0) hm; convert hv using 1 <;> first| rfl | (ext1 z; unfold inSlope; push_cast; ring)

omit h ht in
private lemma mass_era {ℓ:ℕ} (hv:OrbitNorm u U T (inSlope ℓ))(hr:cred U 2): OrbitNorm u (sealPay μ U) (sealPay μ T) (fun z=> -8- (4+2*(ℓ:ℂ))*z) := by
   obtain he:= ((migrate_m hr.choose_spec).tide (fun _ h=> paceVisits (paceFuel h.1))); obtain hV:= Vert_scale u (OrbitNorm.loopScale μ u Q (Vert_scale u hv) he)
   convert hV using 1 <;> first| rfl | (ext1 z; unfold inSlope; ring)
include hA
lemma initial_era : OrbitNorm u (lineIntegral μ X Y A F) (lineIntegral μ X Y (surge A u) F) (fun z=> -8-(4+2*(ℓ:ℂ))*z) :=
  OrbitNorm.plus u (OrbitNorm.plus u (mass_era μ u (x_era μ X Y A u h ht) (funded_x μ X Y A hA h))
    (mass_era μ u (y_era μ X Y A u h ht) (funded_y μ X Y A hA h))) (mass_era μ u (b_era μ X Y A u ht) (funded_b μ X Y A hA h))
end
end YM.MS.ScaleForest.Triangle
