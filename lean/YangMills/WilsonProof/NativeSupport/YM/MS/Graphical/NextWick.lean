import YM.MS.Graphical.NextWick
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Anchoring
import YM.MS.Breeze.Seats

/-!
# Polarized shell integral for a line joining two pinned components

Also at nonzero z; uses the MOMENTUM integral continuation of `Lines.lean`. Like
other graph rules in the present development, we take the graph node as a
sum over all slot allocations. Convenient formula using three loop integrals
with subtraction (just remove intra-component pairs in the Wick contraction
at THIS new edge; this subtraction is not a proper-subgraph subtraction!).
Also see `connectedWing` for its one-integral form before any specialization to
4 dimensions.
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff

variable {G : Gauge} {A E J : Type} {T : Type} {F H : Mob G} {m n : ℕ} {p q : ℤ} {D : Set ℂ}
variable {U : Rip G} {z : ℂ}


lemma tenor_hol (u : ℝ) : Forest Town (fun z=> tenorK z u):= by
  simp_rw [restore_tape]
  exact fun i hi=> (fee_H i hi).mul (by fun_prop)

variable {b : Bool} {f g : ℂ → Mob G} (hz : z∈ Town) (hU : Knot false U)
lemma radialForm (hz : z∈ Town) (hU : Knot b U) (hf : Form0 b F) (y : ℝ) : Form0 b (radialClose U z y F) :=
  (torn hz hf hU).smul _

lemma radial_issue (hz : z∈ Town) (hU : Knot b U) (hf : Form0 b F) (hp : Issue p F) (y : ℝ) :
    Issue (p-2) (radialClose U z y F) := fun m=> Limit.smul _ (cap_ocean hf hU hz hp m)

lemma wickJoin_form (u : Tone.QP) (y : ℝ) (hf : Form0 false F) (hp : Form0 false H) :
    z ∈ Town → Knot false U → Form0 false (wickJoin u U z y F H) := fun h hT=> by
  obtain he:= bring_form u hf
  exact Form0.sub ((radialForm h hT (shuffle_form he hp) y).sub (shuffle_form (radialForm h hT he y) hp))
      (shuffle_form he (radialForm h hT hp y))

lemma wickJoin_issue (u : Tone.QP) (y : ℝ) (hf : Form0 false F) (hp : Issue p F)
    (hg : Form0 false H) (hq : Issue q H) : z ∈ Town → Knot false U →
    Issue (p+q-2) (wickJoin u U z y F H) := fun hz hU=> by
  obtain he:= bring_form u hf; obtain h := bring_issue u hp
  refine fun m=> Limit.sub (Limit.sub (radial_issue hz hU (shuffle_form he hg) (shuffle_issue h hq) y m)
    ((shuffle_issue (radial_issue hz hU he h y) hq m).up ?_))
    ((shuffle_issue h (radial_issue hz hU hg hq y) m).up ?_) <;> omega

lemma radial_hol {U : Rip G} {D : Set ℂ} (hU : Knot b U) (h : D ⊆ Town) (hv : IsOpen D) (hf : Hol D f)
    (he : ∀ i∈D, Sturdy b (f i)) (y : ℝ) : Hol D fun i=> radialClose U i y (f i) :=
  let h0:= wind_he hf (Hop.crate hU.price) h he (fun _ _=> hU.token) hv
  h0.rate (x:=fun i=> tenorK i y) (fun i hi=> tenor_hol y i (h hi))

lemma wickJoin_hol (u : Tone.QP) (y : ℝ) (h : D ⊆ Town) (hv : IsOpen D) (hf : Hol D f)
    (he : ∀ i∈D, Sturdy false (f i)) (hg : Hol D g) (hp : ∀ i∈D, Sturdy false (g i)) :
    Knot false U → Hol D (fun i=> wickJoin u U i y (f i) (g i)) := fun hU=> by
  obtain hW:= bring_hol u hf
  have hw (i :ℂ)(hi : i∈ D) := bring_sturdy u (he i hi)
  have HZ:= radial_hol hU h hv (shuffle_hol hW hg) (fun i hi=> shuffle_sturdy (hw i hi) (hp i hi)) y
  exact (HZ.sub (shuffle_hol (radial_hol hU h hv hW hw y) hg)).sub
    (shuffle_hol hW (radial_hol hU h hv hg hp y))

-- on specialization the pin phases and line measures exactly implement the joins in Fields
open Detect Breeze Rake Latch Latch.Job Outlook
lemma line_meter (G : Gauge) (s : ℝ) : halfD s 0 = PlanetD G s := by rw [halfD_eq]; rfl
lemma kPrice_wallet (h : kPrice F) : F 0 ∈ Wallet G := by
  intro E _ _ w he ht
  refine factorS (High.fig false) _ _ _ (b:=false) ?_ w ht he
  intro E _ _ _ w ht hw
  obtain hp:= h 0 E w
  unfold Cape
  simp only [Breeze.spaceArc,cheap_length,Pi.one_apply,one_zpow,mul_one]; exact hp

lemma canon_at_zero (y s : ℝ) (hf : Form0 false F) :
    radialClose (halfD s) 0 y F 0 = cycle (PlanetD G s) Osc.Snap.planeF (F 0) := by
  rw [← line_meter,halfD_eq]; obtain ht:= c_bo (G:=G) (b:=false) s
  have h:= Outlook.μcanon y ht hf; rw [unitC,LinearMap.smul_apply,
    Wave.port_spec (show (0:ℂ)∈Town by simpa using Town_nat 0) _ ht hf] at h; exact h

lemma canon_at_zero' (y s : ℝ) (hf : Form0 false F) :
    radialClose (halfD s) 0 y F 0 = Breeze.deep G s (F 0):= by
  rw [canon_at_zero y s hf,Breeze.weightC (kPrice_wallet hf.price)]; rfl

lemma phase_zero_placement (u : Tone.QP) : bring u F 0 = chair G u (F 0) := by
  funext w; rfl

theorem joins_after_specialization (u : Tone.QP) (s y : ℝ) (hf : Form0 false F)
    (hg : Form0 false H) : wickJoin u (halfD s) 0 y F H 0 =
      Cabin u (PlanetD G s) Osc.Snap.planeF (F 0) (H 0) := by
  unfold wickJoin; simp only [Pi.sub_apply]
  rw [canon_at_zero' y s (shuffle_form (bring_form u hf) hg)]
  simp only [shuffleRows,canon_at_zero' y s hg,canon_at_zero' y s (bring_form u hf),phase_zero_placement];
  have he := climb_c u 0 (kPrice_wallet hf.price) (kPrice_wallet hg.price) s
  simp only [sub_zero,faith_m] at he
  rw [← he]; change _ = link _ _ _ _ _; rw [link,sign_id]
end YM.MS.Graphical
