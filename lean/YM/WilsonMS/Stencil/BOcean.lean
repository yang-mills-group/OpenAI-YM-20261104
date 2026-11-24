import YM.WilsonMS.Stencil.HBeam
/-!
# Permutations of the physical axes leave the MS integration alone

Using holomorphic profile transport under this fixed signed reindexing. Verify on the
integer D, use temporary momentum cuts for growth in the continuation, then
remove with the proved supplier drift in Plum (no Wick interchange by assumption).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.HBeam
open Function Filter Set Finset MeasureTheory Real
open MS Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment
  Color _root_.YM.MS.Shine Outlook
open scoped Topology ContDiff
variable {G : Gauge} {n m h : ℕ} {I E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {z : ℂ}
  {U : Rip G} {b : Bool} {V : Mob G} (s : Signed)
local notation "X" => rotateMob s G
section support

abbrev shifted {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Touch G n E) : Touch G n E :=
  w.map fun x => (cod s x.1, (grip s).turn.toContinuousLinearMap.comp x.2)

lemma pose_read (w : Touch G n E) (x : E) :
    fieldVal (rotateMob s G V n) w x = signs s (sail w 0) * fieldVal (V n) (shifted s w) x := by
  have he : List.map (mov s) (sail w x) = sail (shifted s w) x := by
    simp only [shifted, sail, List.map_map]
    rfl
  have hz : signs s (sail w x) = signs s (sail w 0) := by
    simp only [signs, sail, List.map_map]
    rfl
  change shiftR s _ _ _ _ = _
  rw [phase, hz, he]
  rfl

lemma rotate_fell {a : I → ℝ} {u : Arc.UScale I} {f : I → Mob G} (h : fell u a f) :
    fell u a (fun i => X (f i)) := by
  intro n E _ _ _ w
  simp_rw [show
      ∀ F : Mob G, fieldVal (X F n) w = (fun x => signs s (sail w 0) * fieldVal (F n) (shifted s w) x)
      from fun F => funext (pose_read s w)]
  exact Costs.L (ContinuousLinearMap.mul ℝ ℂ (signs s (sail w 0))) (h n E (shifted s w))

lemma rotate_hol {D : Set ℂ} {f : ℂ → Mob G} (h : Rock.Hol D f) : Rock.Hol D (fun z => X (f z)) := by
  refine ⟨fun c R hc hr => rotate_fell s (h.price c R hc hr), ?_⟩
  intro n w z hz
  simp_rw [show ∀ u, rotateMob s G (f u) n w = _ from fun u => phase s (f u n) w]
  exact (h.top n _ z hz).const_mul _

lemma rotate_form (hp : Form0 false V) : Form0 false (X V) :=
  ⟨rotate_fell s hp.price, carries s hp.token⟩

lemma rotate_sync {F : ℂ → Mob G} (h : Sync false F) : Sync false (fun p => X (F p)) := by
  obtain ⟨A, hA, hp⟩ := h.eye.price
  exact ⟨⟨⟨A, hA, rotate_fell s hp⟩, rotate_hol s h.eye.sky⟩, fun i hi => carries s (h.vote i hi)⟩

lemma rotate_lift {f : ℂ → Mob G} (h : Lift f V) : Lift (fun p => X (f p)) (X V) := by
  obtain ⟨g, R, hR, h, hx, rfl⟩ := h
  exact ⟨(fun z => X (g z)), R, hR, rotate_hol s h, hx.mono (fun _ hi => congr_arg X hi), rfl⟩

lemma rotate_live {f : ℂ → Mob G} (h : Live f) : Live (fun p => X (f p)) := by
  obtain ⟨V, h⟩ := h
  exact ⟨_, rotate_lift s h⟩
end support
section commute

lemma rotate_arbor (v w : Mob G) (hp : Knot true U) (H : closedF U b) :
    X (arbor U v w) = arbor U (X v) (X w) :=
  funext fun i =>
    (hp.token.turn i (grip s) (fun k => Bool.noConfusion k)).gatherR (v i) (w i) (H i) (H i)

lemma gap_ocean (hV : Form0 false V) (hp : RockB U true) (hz : z ∈ Town) :
    X (ocean z U V) = ocean z U (X V) := by
  have h0 : RockB U false := ⟨hp.toKnot.clearer, hp.gear⟩
  let M := Form0.sync hV
  apply Sync.drape (rotate_sync s (h0.volume0 M)) (h0.volume0 (Form0.sync (rotate_form s hV))) ?_ hz
  intro i
  let T := flagS (grip (n := i) s) G
  let R := beam T
  change R (ocean i U V i) = _
  rw [lamp h0 M, lamp h0 (Form0.sync (rotate_form s hV)), LinearMapRealm]
  refine congr_arg _ ?_
  let Q := grip (n := i) s
  refine
    Pilot.leadC T Q.volume Q.turn.toHomeomorph.measurableEmbedding
      (hp.token.turn i Q (fun i => Bool.noConfusion i)) (V i) (theory hV.price hp.price i)

lemma rotate_ocean (hV : Form0 false V) (hp : Knot true U) (hz : z ∈ Town) :
    X (ocean z U V) = ocean z U (X V) := by
  let W := rotate_form s hV
  let g (j : ℕ) := ocean z (Plum.twine (fade j) U) (X V)
  let HF := oceansLine (steak hV) (newer hp.clearer) hz
  let HG := oceansLine (steak W) (newer hp.clearer) hz
  funext n l
  apply tendsto_nhds_unique (f := fun j => g j n l) ?_ (HG.now n l)
  simp_rw [g, ← gap_ocean s hV (tried hp _ (being _) (sold _)) hz,
    show ∀ V : Mob G, X V n l = _ from fun V => phase s (V n) l]
  exact (HF.now n _).const_mul _

lemma mass_cod (i : Cfield G n) : wfield (cod s i) = wfield i := by
  rcases i with ⟨⟨_ | a, b⟩, t⟩ <;> rfl

lemma rotate_plow (a : ℂ) (t : ℝ) (V : Mob G) : X (plow a t V) = plow a t (X V) := by
  funext n l
  have ht : mass (l.map (mov s)) = mass l := by
    induction l with
    | nil => rfl
    | cons i l ih => rw [List.map_cons, Price_cons, Price_cons, ih]
  change shiftR s G n _ _ = Alps.amount _ _ * shiftR s G n _ _
  rw [phase, phase]
  unfold plow
  rw [ht, mul_left_comm]
  congr 2
  · simp only [signs, sr, List.map_map]
    rfl
  clear ht
  apply congr_arg (V n)
  induction l with
  | nil => rfl
  | cons i l ih =>
    unfold sr at *
    simp only [List.map_cons, ih]
    rcases i with ⟨i, p⟩
    unfold mov
    dsimp only
    rw [map_smul]
end commute
end YM.WilsonMS.HBeam
