import YM.MS.ScaleForest.PageOne

/-!
# Two vertices, a bridge, and its loop closure

These formulas calculate the whole Laurent germ, use no IR removal. They
are meant among other things to let one calculate residues explicitly with
a **convergent** ordinary four-momentum integral. They apply both to
unmarked graphs with two identical cubics and to a marked bridge with two
different vertices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff

variable {G : Gauge} {W : Coat G} {h n : ℕ} {b : Bool} {r : ℤ} {X : Flats G} {F : Mob G}

abbrev classicalPage (P : Mob G) := collapsed (fun _ => P)

theorem bridge_single (K : Rip G) (hr : reverseF K) (W V : Coat G) (m n : ℕ) :
    bridgePages K (Finsupp.single m W) (Finsupp.single n V) =
      Finsupp.single (n+m) (fun z => bridgeG K (W z) (V z)) := by
  rw [bridgePages_eq hr,TreeN, explosionP, Finsupp.sum_single_index]
  · rw [blast_sl]; simp_rw [bridgeG_eq hr]; rfl
  rw [map_zero]
  ext i j w; simp [blap, Finsupp.sum]

theorem closeG_zero (K : Rip G) (z : ℂ) (y : ℝ) : closeG K z y 0 = 0 := by
  funext m w
  have he : loopCarpet K 0 z w = 0 := by funext p; simp [loopCarpet,innerTrace,yeast,Arts.token,fleck]
  have hp (j : ℕ) : pruning j (0 : ℝ × ℝ → ℂ) = 0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hv : Arc.d (0:ℝ × ℝ→ℂ)=0 := by ext; simp [Arc.d]
      rw [spent _ _, ih]; unfold chop; simp_rw [hv]; ext; simp
  simp [closeG,he,hp]

theorem close_single (K : Rip G) (W : Coat G) (m : ℕ) :
    closePages K (Finsupp.single m W) = Finsupp.single (m+1) (fun z : ℂ => closeG K z 0 (W z)) := by
  rw [closePages,Finsupp.sum_single_index]
  simp_rw [Pi.zero_apply,closeG_zero]
  exact Finsupp.single_zero _

theorem scaleZero_invariant (z : ℂ) (F : Mob G) (h : ℕ) : scaleIntegral z h 0 F = scaleIntegral 0 h 0 F := by
  funext m w; simp_rw [scaleIntegral,regulated,vampV]

theorem collapsed_kernel (ht : ClockD b 0 r (classicalPage F)) : Form0 b F := by
  have he := (sunny (clockMoon ht 0)).exists
  rcases he with ⟨z,hz⟩; rw [classicalPage,collapsed,Finsupp.single_eq_same] at hz; exact hz

theorem ct_blind (hC : Coal b h 0 r X) (ht : integratePages h X = classicalPage F) :
    counterterm (integratePages h X) = 0 := by
  obtain ⟨hU,hV⟩ := integrate_sewable (Sewable.mk hC.eye hC.force)
  apply Eq.symm (ct_unique _ _ _ hV hU hC.real)
  · intro y s
    rw [collapsed,Finsupp.single_zero,add_zero,ht]
    obtain hK : Form0 b F := collapsed_kernel (ht ▸ hV.clock : ClockD b 0 r _)
    have he (z : ℂ) : Parade (classicalPage F) h y s z = plow (-(h:ℂ)) s F := by
      simp only [classicalPage,collapsed,page_sl,hikeP,vampV]; simp [Pearl.weight,amount,toll]
    rw [funext he]; exact Live.stays (fseed hK (-(h:ℂ)) s).price
  · exact fun _ => Home.zero _
  exact (cone G).zero_mem

variable (A : LocalVertex G true 4) (B : LocalVertex G b h)
  (K L : LineRule G)

abbrev firstSew := bridge K (vertex A) (vertex B)

def firstForce := (factor b : ℂ) • bridgeG K.half A.symbol B.symbol

def firstSymbol := scaleIntegral 0 h 0 (firstForce A B K)

theorem first_force : (firstSew A B K).instructions.force = classicalPage (firstForce A B K) := by
  unfold firstSew
  rw [instructions,renorm_vertex,renorm_vertex]; unfold sew connect classicalPage collapsed
  dsimp only
  rw [bridge_single K.half K.ok.rev,Finsupp.smul_single]; rfl

theorem first_prep : (firstSew A B K).instructions.prep = classicalPage (firstSymbol A B K) := by
  rw [(computed (firstSew A B K) 0).1, first_force, firstSew]
  rw [show (bridge K (vertex A) (vertex B)).instructions.classicalTerm = 0 from rfl,collapsed,
    Finsupp.single_zero, add_zero]
  unfold classicalPage collapsed firstSymbol
  rw [integrate_single]
  congr 1; exact funext fun z => scaleZero_invariant z _ _

theorem first_pole : (firstSew A B K).instructions.pole = 0 :=
  ct_blind (firstSew A B K|>.accepted.force) (first_prep A B K)

theorem firstResult : (firstSew A B K).instructions.renorm = classicalPage (firstSymbol A B K) := by
  rw [Result.renorm,first_pole,first_prep,collapsed, Finsupp.single_zero,add_zero]

theorem first_integral (s : ℝ) :
    let R t := (factor b : ℂ) • bridgeG (pulse 4 t K.half) A.symbol B.symbol
    plow (-(h:ℂ)) s (firstSymbol A B K) = (fun m w => ∫ t in Iic s, R t m w) ∧
      Gather R s ∧ Shine.Wind (fun t => plow (-(h:ℂ)) t (firstSymbol A B K)) atBot 0 := by
  intro R
  let Z := firstForce A B K
  have hm := (firstSew A B K).accepted.force; rw [first_force] at hm
  have hz := hm.force
  unfold Return at hz
  simp_rw [classicalPage,collapsed,Finsupp.single_eq_same,Pi.zero_apply] at hz
  have H : Shine.Wind (fun s => plow (-(h:ℂ)) s Z) atBot 0 := hz.exists.choose_spec
  have he : kPrice Z := (collapsed_kernel hm.eye).price
  have upscale (t : ℝ) : plow (-(h:ℂ)) t Z = R t := by
    unfold R Z firstForce
    rw [← cert,map_smul]
    congr 1
    rw [bridgeG_eq (a_rev t 4 K.ok.rev),bridgeG_eq K.ok.rev, cert]
    obtain ht := air_tree (a := 4) (b:=-(4:ℂ)) (c := -(h:ℂ))
      (F:=A.symbol) (H:=B.symbol) t K.ok.rev
    rw [B.scaling t, show plow (-4) t A.symbol=A.symbol by simpa using A.scaling t] at ht
    simpa using ht.symm
  have hc : firstSymbol A B K = progress (h+1) (-(h:ℂ)) Z := by
    rw [firstSymbol,evaluated he (fun _=>H) (by simp) (by simp) ]; simp [Z,Bless]
  rw [hc]
  rw [← funext upscale]; refine ⟨?_, integrable_noLoop he H s, frame_lim⟩
  rw [frame_time]; unfold wood
  rw [Mell.peer he H]; rfl

/-- General rule: works with any graph family whose instruction `renorm`
is a `classicalPage`. -/
theorem close_form (K : LineRule G) {T : GraphSum G b h} (hT : T.instructions.renorm=classicalPage F) :
    (loop K T).instructions.force= pageOne (fun z => closeG K.half z 0 F) ∧
      Lift (fun z => closeG K.half z 0 F) (closeG K.half 0 0 F) := by
  constructor
  · rw [show (loop K T).instructions.force = closePages K.half T.instructions.renorm from rfl,hT]
    exact close_single K.half (fun _=> F) _
  have H : Form0 b F := collapsed_kernel (hT ▸ T.accepted.usable.clock : ClockD b 0 T.slots _)
  have ht := Lift.cycle (Lift.stays H.price) (K.ok.forms b) (Eventually.of_forall fun _ => H.token)
  obtain ⟨R,hR,hp⟩ := fee_T 0
  simp_rw [closeG_eq]; exact Lift.high ht hp hR

theorem primitive_laurent (K : LineRule G) {T : GraphSum G b h} (hT : T.instructions.renorm = classicalPage F) :
    let W := fun z => closeG K.half z 0 F
    let X := (loop K T).instructions
    X.prep = integratePages h (pageOne W) ∧
      X.pole = taylorPole h W ∧
      ∀ s y, Lift (Parade X.renorm h y s) (oneLoopFinite h W s y) := by
  intro W X
  obtain ⟨ht,hL⟩ := close_form K hT; change X.force = pageOne W at ht
  have hu := simple_pole_rule hL (ht ▸ same_pact X.force) (loop K T|>.accepted.force)
  exact ⟨congr_arg (integratePages h) ht, hu.1, fun s y => hu.2 y s⟩

/-- The two-vertex version. -/
theorem twoVertex_laurent :
    let W := fun z => closeG L.half z 0 (firstSymbol A B K)
    let X := (loop L (firstSew A B K)).instructions
    X.prep = integratePages h (pageOne W) ∧
      X.pole = taylorPole h W ∧
      ∀ s y, Lift (Parade X.renorm h y s) (oneLoopFinite h W s y) :=
  primitive_laurent L (firstResult A B K)

end YM.MS.ScaleForest
