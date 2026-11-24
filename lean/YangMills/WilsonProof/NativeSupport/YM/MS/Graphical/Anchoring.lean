import YM.MS.Graphical.Anchoring
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Lines
import YM.MS.Fiddle.Born

/-!
# Multiple pins: ambient algebra BEFORE regulator removal

Use phase only on the four **physical** axes. The extra dimensions in the
regularization are for open *momentum* spaces, not changes of the marked
positions. The displacement argument is from the anchor (least index).
A useful formulation uses the shuffle product. `bring` moves a pin or an
anchored connected component to the required displacement; `shuffleRows`
then can be used for taking the contractions of one component with another
(the placement character here is exactly `Tone.bill`, `exp(+i pairing z q₄)`),
with no artificial momentum-conservation condition for either of them.
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff

variable {G : Gauge} {A E J : Type} {a b : J→ℝ} {T : Type}
variable {F H : Mob G} {f g : J → Mob G} {m n : ℕ} {p q : ℤ} {D : Set ℂ}




lemma bring_shift (z : Tone.QP) (K : Spin (L m)) (hp : K.within false) (p : SectorP m) :
    phase m z (K.turn p)=phase m z p:= by
  have he := K.rad (Left (Nat.zero_le m) z) p
  rw [hp rfl, farApart (Nat.zero_le m), farApart (Nat.zero_le m) (Left (Nat.zero_le m) z) p] at he
  simp only [leftCl, Cr_down,Arts.pair_zero,add_zero] at he
  unfold phase Tone.bill; rw [he]

lemma phase_up (h : m ≤ n) (z : Tone.QP) (p : SectorP m) :
    phase n z (Left h p) = phase m z p := by
  unfold phase; congr 1
  change Cl (Nat.zero_le n) _ = _
  rw [show ∀ x, Cl (Nat.zero_le n) x = Cl (Nat.zero_le m) (Cl h x) from fun x => funext fun i=> ?_]; swap; · rfl
  rw [leftCl]

lemma bring_sturdy (u : Tone.QP) (h : Sturdy false F) : Sturdy false (bring u F):= by
  constructor
  · intro m K hp; funext l
    let P:=flagS K G; let c:=phase m u (net l)
    rw [show beam _ (bring u F m) l=beam P (c • F m) l from ?_,map_smul,h.turn m K hp]; rfl
    apply Pilot.offset P _ _ l (u:=net l) _ rfl
    intro i hi; unfold bring; rw [hi, show P.volp (net l)=K.turn (net l) from rfl, bring_shift u K hp]
    rfl
  intro m n h' i; unfold bring; rw [lifts_net,phase_up,h.grows]

lemma shuffle_sturdy {b : Bool} (hf : Sturdy b F) (hg : Sturdy b H) : Sturdy b (shuffleRows F H) := by
  constructor
  · intro m K hp; unfold shuffleRows; rw [circle_prod, hf.turn m K hp,hg.turn m K hp]
  intro m n ht i; unfold shuffleRows; rw [scattered, scattered, scatter_up]
  simp_rw [hf.grows ht,hg.grows ht]

lemma bring_cost (u : J → Tone.QP) (hf : fell 0 a f) (hv : ∃ r:ℝ,∀ i : J, ‖u i‖ ≤ r) :
    fell 0 a fun i=> bring (u i) (f i) := by
  intro m E _ _ _ w; unfold fieldVal bring phase; simp_rw [sail_net]
  obtain ⟨r,hr⟩:= hv
  exact Fiddle.pulse_bill ((Cl (Nat.zero_le m)) ∘L net w) (hf m E w)
     ⟨max 1 r,lt_max_of_lt_left zero_lt_one,0,fun i p _=> by
       simpa using (hr i).trans (le_max_right 1 r)⟩

lemma shuffle_cost (hf : fell 0 a f) (hg : fell 0 b g) :
    fell 0 (a*b) fun i=>shuffleRows (f i) (g i) := by
  intro m E _ _ _ w; unfold fieldVal shuffleRows; simp_rw [scattered, sail_scatter]
  exact gather_bound w (fun l r _ => Costs.mul (hf m E l) (hg m E r))

lemma bring_form (u : Tone.QP) (hf : Form0 false F) : Form0 false (bring u F) :=
  ⟨bring_cost (fun _:Unit=>u) hf.price ⟨_,fun _=>le_rfl⟩, bring_sturdy u hf.token⟩

lemma shuffle_form (hf : Form0 false F) (hp : Form0 false H) : Form0 false (shuffleRows F H) := by
  refine ⟨?_,shuffle_sturdy hf.token hp.token⟩
  convert shuffle_cost hf.price hp.price using 1; ext; simp

lemma bring_issue (u : Tone.QP) (hf : Issue p F) : Issue p (bring u F) :=
  fun m l h => by unfold bring; rw [hf m l h, mul_zero]
lemma shuffle_issue (hf : Issue p F) (hp : Issue q H) : Issue (p+q) (shuffleRows F H) :=
  fun m=> Limit.pair (hf m) (hp m)

variable {x y : ℂ → Mob G}

lemma bring_hol (u : Tone.QP) (hf : Hol D x) : Hol D (fun i=> bring u (x i)) :=
  ⟨fun c r hp hx=> bring_cost (fun _ : closedBall c r=>u) (hf.price c r hp hx) ⟨_,fun _=>le_rfl⟩,
    fun m l z hz=> (hf.top m l z hz).const_mul _⟩

lemma scatter_hol {f : ℂ→ Shared A ℂ} (l : Legs A) (p : Sector A)
    (hp : ∀ i j, Split i j l → Forest D (fun t=> f t i j)) : Forest D (fun t=> scatter p l (f t)):= by
  induction l generalizing f with
  | nil=> exact hp _ _ .nil
  | cons i l ih=> exact ih (fun u v he t ht=> (hp _ _ he.left t ht).add ((hp _ _ he.right t ht).const_mul _))

lemma shuffle_hol (hx : Hol D x) (hy : Hol D y) : Hol D (fun i=>shuffleRows (x i) (y i)) := by
  constructor
  · intro c r hr h; convert shuffle_cost (hx.price c r hr h) (hy.price c r hr h) using 1; ext; simp
  intro m l; unfold shuffleRows; simp_rw [scattered]; exact scatter_hol l _
      (fun i j _ t ht=> (hx.top m i t ht).mul (hy.top m j t ht))
end YM.MS.Graphical
