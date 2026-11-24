import YM.LocalTaylorR2.Kiln.Movable

/-! # Take current only on the interior, repay through the same spot (including mask & angular charges). Outstanding probability or factor interpretation left in Local. See Stargaze. -/
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

def living (X:Coat T F)(a η:ℝ)(A:ℕ→ Atom G d)(R:Rep G f)(i:Trans f) (u:Directions G f):ℝ:= translateValue R.p A η (X.input u) i * pane X a A i u

def bill (k k' η x: ℝ) (A:ℕ→ Atom G d)(i:Trans f):= |η| * (if (A i.2.2).length ≤ till x then |k| else |k'|) * (A i.2.2).magnitude
def seating (l:ℕ)(x:ℝ)(S:StepData c f) (A:ℕ→ Atom G d)(i:Trans f):ℝ:=1+((coverNumber (radiusB x) (atomFoot S.ratio l (radiusB x) A i):ℝ)+(atomCharge A i : ℝ))
lemma munch (A:ℕ→ Atom G d) (i:Trans f): 0≤ (A i.2.2).magnitude:= by unfold Atom.magnitude; positivity
private lemma cloaks {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {F:E→ℝ} {a b c s :ℝ}{p:E}
    (h:Brush j a b F p) (hh: b ≤  c * s)(hc:1 ≤ c)(hs:0 ≤ s): Brush j (a * c^j) s F p:=by
  have ha:=h.nonneg; have hb:=h.pos; have ht:0≤c:=zero_le_one.trans hc
  refine ⟨h.smooth,hs,fun i hi=>?_⟩; calc
   _ ≤ a*b^i:= h.order i hi
   _ ≤ a*(c*s)^i:=by gcongr
   _ ≤ _:=by rw [mul_pow,← mul_assoc]; gcongr
lemma sit_ge (l:ℕ)(x:ℝ)(S:StepData c f) (A:ℕ→ Atom G d)(i:Trans f):1 ≤ seating l x S A i:= by unfold seating; exact le_add_of_nonneg_right (by positivity)
variable {E :Type}[NormedAddCommGroup E][NormedSpace ℝ E]{y:E}{V:E→ Config G c}{u:E→ Directions G f}{w:E→ Air f G}{z :Air f G} {J:Basecamp G} {B v s' A' q b η a :ℝ}
omit [NormedAddCommGroup E][NormedSpace ℝ E] in
lemma overlay (A:ℕ→ Atom G d)(i:Trans f) {U U':Config G f} (h: Armor X (2*a) (u y) U U')(hh:0<a*X.t)(hp:pane X a A i (u y) ≠ 0) : Agrees (inspected ((A i.2.2).footprint i.2.1)) (pull i.1 0 U) (pull i.1 0 U'):= (plastic h hh).torrid _ _ hp

/-- At a clutch on *fine* corners. DIM/long both avoid making V-clean
 assumptions. Purchase B marker of `central`, but normalize to unit per-seating for uniform cap.
 Keep true orientation η (e.g. actual beta). -/
lemma count_in (a η:ℝ)(x : E)(p:ℕ)(_hh: Mode V x j v)(ht:Clutch X z a R.beta s x j V u w) (_hP:Room P S T X.x)(_hk:(A i.2.2).Invariant)
    (hz:1≤q)(hu:0≤B)(he : Brush j 1 (B * q) (fun t=> pane X a A i (u t)) x)
    (hy : light X A i → ¬ dim X i → (¬ (fun t=> pane X a A i (u t))=ᶠ[𝓝 x] fun _=>0) →
       Brush j (|A'| *(A i.2.2).magnitude) 1 (fun t=> (A i.2.2).unmasked (pull i.1 0 (X.input (worldZ X R.beta z))) i.2.1- pollen J (vary X (V t)) A i p (u t)) x) :
    let f t:= living (vary X (V t)) a η A R i (u t) - lantern J (vary X (V t)) a η A R i p (u t)
    Brush j (bill (|A'| *(1+B)^j) ((2:ℝ)^d*(1+B)^j) η X.x A i) q f x := by
  intro f; let g t:= pane X a A i (u t); let Z t:= vary X (V t); let P t:= (Z t).input (u t); let U:= X.input (worldZ X R.beta z)
  let L t:= pollen J (Z t) A i p (u t); have ha := ht.pulse; have hA:= munch A i; have hq:0 ≤ q:= zero_le_one.trans hz
  unfold bill; split_ifs with hx; swap
  · let g' t:= translateValue R.p A η (P t) i
    have h : |translateValue R.p A η U i|≤ |η| *((A i.2.2).magnitude* (2:ℝ)^d):= by unfold translateValue; rw [abs_mul]; gcongr; exact Atom.placed_bound ..
    apply ((cloaks (he.smul (translateValue R.p A η U i)) (c:=1+B) (by linarith : B*q ≤ (1+B)*q) (by linarith) hq).climb _ le_rfl).shimmy
    · filter_upwards [ht.patch] with t ht; unfold f lantern living; rw [if_neg (show ¬ light (Z t) A i from hx),sub_zero]
      change g' t * g t= _* g t; by_cases hm : g t=0; · rw [hm,mul_zero,mul_zero]
      have h := (plastic (X:=Z t) ht (show 0<_ from ha)).torrid (inspected ((A i.2.2).footprint i.2.1)) i.1 (show _≠_ from hm)
      exact congr_arg (· * g t) (congr_arg (η * ·) (placed_local _ _ _ _ _ h)) -- shadow a alias
    · rw [Real.norm_eq_abs,mul_one,abs_of_nonneg (by positivity : 0≤(2:ℝ)^d*(1+B)^j)]; apply (mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (1+B)^j)).trans_eq; ring
  by_cases hl: dim X i; · apply Brush.zi _ (by positivity) hq; filter_upwards with t; unfold f living lantern; rw [if_pos (show light (Z t) A i from hx), if_pos (show dim (Z t) i from hl),sub_self]
  let r := switch R A i U
  have hr:‖η*r‖ ≤|η|:= by unfold r switch; split_ifs <;> simp
  let q' t:= (A i.2.2).unmasked (pull i.1 0 U) i.2.1-L t
  have h : f =ᶠ[𝓝 x] fun t=> (η*r)*(q' t*g t):= by
    filter_upwards [ht.patch] with t ht; unfold f living lantern; rw [if_pos (show light (Z t) A i from hx), if_neg (show ¬ dim (Z t) i from hl)]
    change (translateValue R.p A η (P t) i)*g t- η*(L t * switch R A i (P t))*g t= _; by_cases hp : g t=0; · rw [hp,mul_zero,mul_zero,mul_zero,mul_zero,sub_self]
    have h : Agrees (inspected ((A i.2.2).footprint i.2.1)) (pull i.1 0 (P t)) (pull i.1 0 U):= overlay (X:=Z t) _ _ ht ha hp
    rw [switching _ _ _ h, show (translateValue R.p A η (P t) i)=(translateValue R.p A η U i) from congr_arg (η*·) (placed_local _ _ _ _ _ h), clearcost]
    unfold q' r; ring
  by_cases hp : g=ᶠ[𝓝 x] fun _=>0; · apply Brush.zi (h.trans (hp.mono fun i hi=> by change _ * (_ * g i)=(0:ℝ); rw [show g i=0 from hi,mul_zero,mul_zero])) (by positivity) hq
  apply ((cloaks (((hy hx hl hp).paints he).smul (η*r)) (by linarith : 1+B*q ≤ (1+B)*q) (by linarith) hq).climb _ le_rfl).shimmy h
  rw [mul_one,abs_of_nonneg (by positivity : 0≤ |A'| *(1+B)^j)]; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (by positivity)) (by positivity)) (le_of_eq ?_); ring
end YM.LocalTaylorR2.Kiln
