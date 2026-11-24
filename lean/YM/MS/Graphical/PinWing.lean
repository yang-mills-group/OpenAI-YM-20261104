import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.NextWick

/-!
# Joining pinned components in the Arc rule with just a single loop integral, subtracting intra-pairs
before momentum integration

Useful for small-scale bounds. Anchor shift by `u` must be paid for on the
left operand also when this is a connected (≥2 pins) component; the right
side contains the minimum pin in the whole row.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff
variable {G : Gauge} {E A J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : Bool}
    {F H : Mob G} {U : Rip G} {z : ℂ} {m n : ℕ}

-- core at scalar external row with any linear read on finite collection of words
abbrev WingDomain (m : ℕ) (E : Type) := (SectorP m×ℝ) × E

def readWing (U : Rip G) (z : ℂ) (F : Mob G) (L : E → Rack G m→ℂ) (p : WingDomain m E) :=
   L p.2 (pulls (Nat.le_succ m) (Wtr z U F (slideA (Nat.lt_succ_self m) p.1)))

lemma readWing_eval (U : Rip G) (z : ℂ) (F : Mob G) (w : Touch G m E):
    readWing U z F (fun i f=> f (sail w i)) = wing z U F w := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma read_mirror (hf : Sturdy b F) (hU : Ruddy b U) (z : ℂ) (L : E → Rack G m →ℂ) :
    mirror (readWing U z F L) := by
  intro x y w; apply congr_arg (L w); funext i
  obtain he:=wing_mirror hf hU z (ray i) x y 1
  simp only [wing,ray_sail] at he; exact he

lemma swoop_minus {f g : WingDomain m E→ℂ} (hf : Ultra f) (hg : Ultra g)
    (h : mirror f) (hx : mirror g) (hz : z∈ Town) :
    swoop z (Px m) m (f-g)=swoop z (Px m) m f - swoop z (Px m) m g := by
  have he : carpet (Px m) (f-g)=carpet (Px m) f-carpet (Px m) g:= by
    ext w; exact integral_sub ((Q.Gmajor (Px m) hf ()).values w) ((Q.Gmajor (Px m) hg ()).values w)
  unfold swoop; rw [he]
  have ht : Ultra (carpet (Px m) f) := Q.Gquiet (Px m) hf; have hy : Ultra (carpet (Px m) g) := Q.Gquiet (Px m) hg
  apply eq_sub_of_add_eq
  rw [← core_pl (show Ultra (carpet (Px m) f-carpet (Px m) g) from ht.sub hy) (show Reflect (carpet (Px m) f-carpet (Px m) g) from ?_)
    hy (mirror_r (Px m) hx) hz,sub_add_cancel]
  exact fun y t=> congr_arg₂ (·-·) (mirror_r (Px m) h y t) (mirror_r (Px m) hx y t)

variable {L : E → Rack G m → ℂ}
lemma readWing_integral (hf : Form0 b F) (hu : Knot b U) (hx : z ∈ Town)
    (hU : Ultra (readWing U z F L)) (x : E) (hz : L x ∈ Centre _) :
    swoop z (Px m) m (readWing U z F L) x = L x (ocean z U F m):= by
  obtain ⟨h,_,HP⟩:= catalog hu hf hx hz
  rw [← HP]; unfold swoop coreC fetching fetchP; simp only [Pi.smul_apply]

  refine congr_arg (gage m • ·) (integral_congr_ae (Eventually.of_forall fun i=>?_))
  apply congr_arg (cloud z i • ·)
  apply Fiber.pruneC (f := carpet (Px m) (readWing U z F L)) x (1:ℝ) ((Q.Gquiet (Px m) hU).smooth ()) (h.smooth ())
     (show ∀ r, carpet (Px m) (readWing U z F L) (r,x)=strand (L x) U F z (r,(1:ℝ)) from ?_) (m+1) i
  intro r
  have he := cent_arguments (Px m) hz (f:=fun y w=> wing z U F (ray w) ((y,r),1))
      (fun i=> (Q.Gmajor (Px m) (exact_test hf.price hu.price (ray i) z) ()).values (r,1));
  simp_rw [wing,ray_sail] at he; unfold carpet strand; simp_rw [carpet,wing,ray_sail]; exact he.2

def leftMesh (F H : Mob G) (U : Rip G) (z : ℂ) (w : Touch G m E) : WingDomain m E→ℂ :=
  readWing U z F (fun i f => product (field Landau.parity) f (H _) (sail w i))

def rightMesh (F H : Mob G) (U : Rip G) (z : ℂ) (w : Touch G m E) : WingDomain m E→ℂ :=
  readWing U z H (fun i f => product (field Landau.parity) (F _) f (sail w i))

/-- Arc test function of the joined cross line. The two subtractions here
are the left-left and right-right ANY-two Wick pairs (not UV subtractions).
The separate phase in the loop is made manifest in `WingLink.lean`. -/
def connectedWing (u : Tone.QP) (F H : Mob G) (U : Rip G) (z : ℂ) (w : Touch G m E):=
  wing z U (shuffleRows (bring u F) H) w - leftMesh (bring u F) H U z w - rightMesh (bring u F) H U z w

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma minus_mirror {f g : WingDomain m E→ℂ} (h : mirror f) (hx : mirror g) : mirror (f-g) :=
  fun x y t=> congr_arg₂ (·-·) (h x y t) (hx x y t)

lemma connected_reflect (x : Tone.QP) (hp : Sturdy false F) (ht : Sturdy false H)
    (h : Ruddy false U) (z : ℂ) (w : Touch G m E) : mirror (connectedWing x F H U z w):= by
  have he:= bring_sturdy x hp
  apply minus_mirror (minus_mirror (wing_mirror (shuffle_sturdy he ht) h z w) (read_mirror he h z _))
    (read_mirror ht h z _)

lemma quiet_scatter {T K : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] {a : J → ℝ} {p : Sector K}
    (w : List K) {f : J → T × E → Shared K ℂ}
    (h : ∀ i j, Split i j w → quiet 0 (fun k x=> f k x i j) a) :
    quiet 0 (fun k x=> scatter p w (f k x)) a:= by
  induction w generalizing f with
  | nil=>exact h _ _ .nil
  | cons s l ih=>
    apply ih; intro i j hi; exact (h _ _ hi.left).add
      ((h _ _ hi.right).L (ContinuousLinearMap.mul ℝ ℂ (cross (p s) (degree p i))))

variable [FiniteDimensional ℝ E]
lemma leftMesh_ultra (hf : kPrice F) (hp : kPrice H) (hU : rPrice U) (w : Touch G m E) (z : ℂ):
    Ultra (leftMesh F H U z w) := by
  unfold Ultra leftMesh readWing; simp_rw [scattered, sail_scatter];
  apply quiet_scatter; intro i j _
  convert! (exact_test hf hU i z).mul (Bound.linear (ContinuousLinearMap.snd ℝ (SectorP m×ℝ) E)
    (hp m E j)) using 1; ext; simp

lemma rightMesh_ultra (hf : kPrice F) (hg : kPrice H) (hU : rPrice U) (w : Touch G m E) (z : ℂ):
    Ultra (rightMesh F H U z w) := by
  unfold Ultra rightMesh readWing; simp_rw [scattered, sail_scatter]; apply quiet_scatter
  intro i j _; simp_rw [mul_comm (F _ _)]; convert! (exact_test hg hU j z).mul (Bound.linear
    (ContinuousLinearMap.snd ℝ (SectorP m×ℝ) E) (hf m E i)) using 1; ext; simp

lemma connectedWing_ultra (u : Tone.QP) (w : Touch G m E) (z : ℂ) (hf : kPrice F)
    (hp : kPrice H) (hU : rPrice U): Ultra (connectedWing u F H U z w) := by
  obtain h : kPrice (bring u F):= bring_cost (fun _ :Unit=>u) hf ⟨_,fun _=>le_rfl⟩
  have ht : kPrice (shuffleRows (bring u F) H):= by convert shuffle_cost h hp using 1; ext; simp
  exact ((exact_test ht hU w z).sub (leftMesh_ultra h hp hU w z)).sub (rightMesh_ultra h hp hU w z)

theorem connected_integral (u : Tone.QP) (y : ℝ) (w : Touch G m E) (x : E)
    (hf : Form0 false F) (hp : Form0 false H) (hx : Knot false U) (hz : z∈ Town) :
    tenorK z y * swoop z (Px m) m (connectedWing u F H U z w) x =
        wickJoin u U z y F H m (sail w x):= by
  let P:=bring u F; let T:=shuffleRows P H; obtain h:=bring_form u hf; obtain ht:=shuffle_form h hp
  obtain hA:=exact_test ht.price hx.price w z
  obtain HA:=wing_mirror ht.token hx.token z w
  obtain hB:=leftMesh_ultra h.price hp.price hx.price w z
  obtain hC:=rightMesh_ultra h.price hp.price hx.price w z
  obtain HB : mirror (leftMesh P H U z w):=read_mirror h.token hx.token z _
  obtain HC : mirror (rightMesh P H U z w):=read_mirror hp.token hx.token z _
  have he (R : Mob G)(h : Form0 false R) :
      tenorK z y * swoop z (Px m) m (wing z U R w) x = radialClose U z y R m (sail w x):= by
    have he:= congr_fun (oceanic (fun i=>const_sc (‖2*(z-i)‖)) h.price hx.price
      (fun _=>zero_le_one) () w (Z:=fun _=>z)) x; exact congr_arg (tenorK z y * ·) he.symm
  unfold wickJoin connectedWing
  rw [swoop_minus (f:=wing z U (shuffleRows (bring u F) H) w - leftMesh (bring u F) H U z w) (hA.sub hB) hC (minus_mirror HA HB) HC hz, swoop_minus hA hB HA HB hz]
  simp only [Pi.sub_apply,mul_sub, he (shuffleRows (bring u F) H) ht];
  unfold leftMesh rightMesh
  rw [readWing_integral h hx hz hB x ?_, readWing_integral hp hx hz hC x ?_]
  · unfold shuffleRows; simp only [radialClose_eq_ocean,Pi.smul_apply,map_smul,LinearMap.smul_apply,smul_eq_mul]
  all_goals
    simp_rw [scattered]; apply cent_gather; intro a b hab
    first | exact cent_scale _ _ (centroid _)
          | (simp_rw [mul_comm (_:ℂ) (H m _)]; exact cent_scale _ _ (centroid _))
end YM.MS.Graphical
