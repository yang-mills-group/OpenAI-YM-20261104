import YM.Progress.DIRECTED_RECIPE.Pellets
import YM.Integration.FullQLocalRetainedOutput
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Intake

/-! Real dormant places for each prescribed ordinary source on any admitted
    physical representation, leaving the complete submitted hard bank at its
    original addresses. The old signed density is preserved on every field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalInheritedRegularSlots
open Function Set Lattice Wilson RG Marker Overlay
open RG.Shoot Pressure Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection
open PhysicalNext PhysicalNext.Repeat ConnectedActivityE6
open RG3.Forms RG3.Held RG3.Script.Picnic
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open scoped Classical

variable {G : Gauge} {n : Side} (Y : Rep G n)

def entry : ℕ ↪ ℕ := use (regularKeys n) Y.activities.reg

def activities : Activities G n :=
  {Y.activities with reg:=(drawer G n).reg, E:=stuff (entry Y) Y.activities.E}

def carrier : Rep G n := {Y with activities:=activities Y}

theorem original : Readdress Y.p (entry Y) (Function.Embedding.refl ℕ) Y.activities (activities Y) where
  same_reg i := congrArg Prod.fst (book (regularKeys n) Y.activities.reg i)
  sup _ := rfl
  inv _ := rfl
  emits i := stuffed (entry Y) Y.activities.E i
  kernels _ := rfl
  restE _ h := blank _ _ h
  restK i h := (h ⟨i,rfl⟩).elim
  admits _ _ h := h

theorem reserved (z : RegularAddress n) (tag : ℕ) :
    (carrier Y).activities.reg (blankRow n (z,tag))=z ∧
    (carrier Y).activities.E (blankRow n (z,tag))=0 :=
  ⟨congrArg Prod.fst (recorded (regularKeys n) z tag),
    (original Y).restE _ (distinct (regularKeys n) Y.activities.reg z tag)⟩

theorem different {z w : RegularAddress n} {i j : ℕ} (h : i≠j) :
    blankRow n (z,i)≠blankRow n (w,j) := by
  intro eq
  exact h (congrArg Prod.snd ((blankRow n).injective eq))

theorem forced : (carrier Y).activities.forced=Y.activities.forced ∧ (carrier Y).activities.K=Y.activities.K :=
  ⟨rfl,rfl⟩

def moves {s : Signed} {b : Site n} (h : Y.activities.Moves s b) : (activities Y).Moves s b := by
  let g := regMap (destination s b)
  let M := rearrange (regularKeys n) g h.ep
  have align i : g (Y.activities.reg i)=Y.activities.reg (h.ep i) :=
    reg_ext (h.reg_site i).symm (h.reg_support i).symm
  have moved i : M (entry Y i)=entry Y (h.ep i) := move_stock (regularKeys n) g h.ep Y.activities.reg align i
  have label i : (activities Y).reg (M i)=g ((activities Y).reg i) :=
    congrArg Prod.fst (stocked (regularKeys n) g h.ep i)
  refine ⟨M,h.kp,(fun i => congrArg RegularAddress.site (label i)),
    (fun i => congrArg RegularAddress.support (label i)),h.forced_support,h.forced_inventory,h.forced_tests,?_,h.valuesK⟩
  intro i U
  change stuff (entry Y) Y.activities.E (M i) U=stuff (entry Y) Y.activities.E i (pull s b U)
  by_cases hi : i∈range (entry Y)
  · obtain ⟨j,rfl⟩ := hi
    rw [moved,stuffed,stuffed]
    exact h.valuesE j U
  rw [blank _ _ (unused moved hi),blank _ _ hi]
  rfl

theorem valid {e k : ℝ} (h : Y.activities.Valid Y.p e k) : (activities Y).Valid Y.p e k :=
  ⟨(original Y).regular h.regular,
    ⟨h.forced.sym,h.forced.symtest,h.forced.meas,h.forced.meas_test,
      h.forced.reads,h.forced.reads_test,h.forced.permit⟩,
    fun s b => (h.moves s b).map (moves Y),
    (original Y).Ebound h.boundE,(original Y).Kbound h.boundK⟩

theorem lawful {σ C Λ e k : ℝ} (paid : Y.Lawful σ C Λ e k) : (carrier Y).Lawful σ C Λ e k :=
  ⟨paid.paths,valid Y paid.labels⟩

theorem intake {c : Side} {P : Teller G} {S : StepData c n} {T : Tube G S} {x : ℝ}
    (h : Intake P T x Y) : Intake P T x (carrier Y) :=
  ⟨h.ready,⟨h.received.path,h.received.clip,h.received.temp⟩,lawful Y h.cap,h.exponent,h.height,h.sizes,h.window⟩

theorem exponent (U : Config G n) : (carrier Y).exponent U=Y.exponent U :=
  congrArg (fun a : Config G n → ℝ => Y.v*Fintype.card (Site n)-Y.path.inChannels Y.clip Y.p Y.beta U-a U)
    (original Y).same_sum

theorem density (U : Config G n) : (carrier Y).eval U=Y.eval U :=
  congrArg (fun e : ℝ => Real.exp e*Y.activities.gas Y.p U) (exponent Y U)

variable {V X : Type*} [DecidableEq V] [Fintype V] {Γ : Census V} {o : V → Site n}

def marked (T : Taste X o Y Γ) : Taste X o (carrier Y) Γ where
  menu := ⟨T.menu.origins,T.menu.rays,T.menu.branch,T.menu.marks,T.menu.global,T.menu.regular,T.menu.force⟩
  root := T.root
  tag := T.tag
  site := T.site
  score := T.score

theorem full (T : Taste X o Y Γ) (x : X) (U : Config G n) :
    ((marked Y T).leaf x).density U=(T.leaf x).density U :=
  congrArg (fun e : ℝ => (Real.exp e:ℂ) • (Poly.pass ((T.leaf x).log U)*(T.leaf x).contents.cluster U))
    (exponent Y U)

omit [Fintype V] in
theorem active (T : Taste X o Y Γ) (x : X) (h : (T.leaf x).Active) : ((marked Y T).leaf x).Active :=
  ⟨⟨h.articles.proper,h.articles.pins,h.articles.regular,h.articles.occurs,h.articles.retained,
    h.articles.inspects,h.articles.keeps,h.articles.meas,h.articles.invi⟩,h.captions⟩

variable {V₀ X₀ : Type} [Fintype V₀] [DecidableEq V₀] {Γ₀ : Census V₀} {o₀ : V₀ → Site n}

def budget (T : Taste X₀ o₀ Y Γ₀) {p : BudgetPoint} {w : V₀ → ℝ} {κ a b : ℝ}
    (h : FullBudget p T w κ a b) : FullBudget p (marked Y T) w κ a b where
  white := h.white
  black := h.black
  gold := h.gold
  unitBound := h.unitBound
  active x := active Y T x (h.active x)
  radii := h.radii
  divisor := h.divisor
  white_nonnegative := h.white_nonnegative
  regular i := ⟨(h.regular i).controls⟩
  regular_law := h.regular_law
  black_nonnegative := h.black_nonnegative
  forced := h.forced
  gold_nonnegative := h.gold_nonnegative
  caption := h.caption
  unit_nonnegative := h.unit_nonnegative
  unit := h.unit
  regularTotal := h.regularTotal
  forcedTotal := h.forcedTotal

end YM.Integration.QLocalInheritedRegularSlots
end
