import YM.MSbar.Origin.Spout

/-!
# No gauge change of the bare action

Fields-only and volume-divergence tests. Produce the nonlinear master
relation (and measure at next coefficient) from the finite alphabet. Since
classical θ used these formulations often with divergent volume, stick to
any native coordinates and **not** the infinite-volume orbit itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Origin.Charm
open Function Filter Topology Super Finset
open scoped BigOperators ContDiff
variable {α β M J : Type*} {p : β→Bool} (K : Charm M J β p)
variable [Fintype J] [DecidableEq J] [DecidableEq β] {V : Canal M J} {D : Beamish J}

/-- Keep pin condition--on orthonormal basis. `cry` is corresponding volume-
changing infinitesimal which should be zero with either flat or Haar volume. -/
def Pinch (D : Beamish J) := ∀ a b,D a a b=0
lemma pitch (H : Beats D) (F : Pinch D) (i : J) : peel (K.shade i) (K.trunk D i)=0 := by
   simp only [trunk,peel_smul,peel_sum]; apply smul_eq_zero_of_right
   refine sum_eq_zero fun j _ => sum_eq_zero fun a _ => ?_
   by_cases e : i=j
   · subst j; simp [F i a];
   by_cases b : i=a
   · subst a; rw [H i j i,F i j]; simp
   rw [duplex, (K.grade_ghost j).peel_mix,K.shade_ghost,K.shade_ghost,if_neg e,if_neg b]; simp
variable [Fintype M] [DecidableEq M]

def cry (V : House M→House M) : House M → ℝ := ∑ i, stunt (pick V i) (onePiece i)
lemma cry_ready {V : House M→House M} (H : Eager V 0) : Eager (cry V) 0 := strokeSum fun i _ => stunt_eager (pick_eager H i) _
lemma loose (H : Beats D) (F : Pinch D) (G : ∀ j,Eager (V j) 0) : (∑ i,peel (K.toCanon.leaf i) (K.lift V D i))= ∑ j,mix p (K.ghost j) (K.send (cry (V j))) := by
  rw [Fintype.sum_sum_type]; change (∑ i,peel (K.prime i) (K.poses V i))+(∑ i,peel (K.shade i) (K.trunk D i))=_
  simp only [K.pitch H F,sum_const_zero,add_zero];
  simp_rw [poses,peel_sum,(K.grade_ghost _).peel_mix, prime_ghost, mix_first_zero, zero_add, K.prime_hue, twist_false, one_smul, K.peel_send]
  rw [sum_comm]; apply sum_congr rfl; intro j _; rw [cry,send,bose_sum K.view (f:=fun i => stunt (pick (V j) i) (onePiece i)) (fun i _ => stunt_eager (pick_eager (G j) _) _),mix_sum_last]

def Rings (V : Canal M J) (f : House M→ℝ) := ∀ j, route (V j) f=ᶠ[𝓝 0] 0

def absolute (V : Canal M J) (f : House M→ℝ) := ∀ j, route (V j) f+cry (V j)=ᶠ[𝓝 0] 0

omit [DecidableEq J] in
lemma operate_null (H : ∀ j,Eager (V j) 0) {f : House M→ℝ} (h : Eager f 0) (F : Rings V f) : K.operate V D (K.send f)=0 := by rw [operate_send _ H h]; apply sum_eq_zero; intro j _; rw [send,bose_congr K.view (F j),bose_zero,mix_last_zero]

structure Strength (D : Beamish J) (V : Canal M J) : Prop where
  beats : Beats D
  chased : Chased D
  pinched : Pinch D
  ready : ∀ j,Eager (V j) 0
  turns : TurnsAlong V D

omit [DecidableEq J] in
def classic (V : Canal M J) (D : Beamish J) (S : House M→ℝ) : Term β := K.toCanon.dress (K.lift V D) (K.send S)

omit [DecidableEq J] in
lemma classic_grade (V : Canal M J) (D : Beamish J) (S : House M→ℝ) : Grade p false (K.classic V D S) := K.toCanon.dress_grade (K.grade_send _) (K.grade_lift V D)
omit [DecidableEq J] in
lemma classic_order (H : ∀ j,Eager (V j) 0) (D : Beamish J) {S : House M→ℝ} (h : Eager S 0) : Ordered p (K.classic V D S) := K.toCanon.dress_order (K.order_send h) (K.order_lift H D)

variable [Fintype β] {S T : House M→ℝ}
lemma Strength.classical (F : Strength D V) (h : Eager S 0) (H : Rings V S) :
    (1/2:ℂ) • cross p K.toCanon.ties (K.classic V D S) (K.classic V D S)=0 := by
  unfold classic; rw [K.toCanon.classical_master (K.grade_send _) (K.stand_send S) (K.grade_lift _ _) (K.stand_lift _ _)]
  change K.operate V D (K.send S)-∑ a,mix p _ (K.operate V D _)=0; simp [K.operate_null F.ready h H, K.nil_lift F.beats F.chased F.ready F.turns]
lemma Strength.ratio (F : Strength D V) (hs : Eager S 0) (ht : Eager T 0) (J : absolute V T) :
    bell K.toCanon.ties (K.classic V D S)+cross p K.toCanon.ties (K.classic V D S) (K.send T)=0 := by
  unfold classic; rw [K.toCanon.classical_trace (K.order_send hs) (K.stand_send _) (K.order_lift F.ready _) (K.stand_lift _ _),
                       K.toCanon.classical_derivative (K.grade_send _) (K.stand_send S) (K.grade_lift _ _) (K.stand_lift _ _) (K.stand_send _)]
  rw [K.loose F.beats F.pinched F.ready]
  change _+K.operate V D _=0; rw [operate_send _ F.ready ht,←sum_add_distrib]; refine sum_eq_zero fun i _ => ?_; rw [add_comm,←mix_add_last,send,send,← bose_add K.view (route_eager (F.ready i) ht) (cry_ready (F.ready i)),bose_congr _ (J i),bose_zero,mix_last_zero]
lemma Strength.protect (F : Strength D V) (H : Rings V T) (h : Eager T 0) : cross p K.toCanon.ties (K.classic V D S) (K.send T)=0 := by
  unfold classic; rw [K.toCanon.classical_derivative (K.grade_send _) (K.stand_send S) (K.grade_lift _ _) (K.stand_lift _ _) (K.stand_send _)]; exact K.operate_null F.ready h H
end YM.MSBar.Origin.Charm
