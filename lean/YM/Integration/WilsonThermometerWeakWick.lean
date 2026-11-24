import YM.Integration.WilsonThermometerWeakTaylor
import YM.Next.RANK.RayGate

/-! Linear-cell and same-insertion Wick errors of a genuine measured stable
section. The bare rank zero is included in the polynomial read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWick
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open PhysicalNext.Repeat.Legato Trace.Physical GermGraph
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops Asymptotics
open Perch Glimmer LiftMark Beamer MvPolynomial Atlas Tariffs Planned.GuardedAtom
open WilsonThermometerWeakTaylor
open scoped Classical ContDiff BigOperators Topology
variable {G:Gauge} {d D:ℕ} {F:Frame G d} (H:Hol G)

theorem angular (degree:d≤D) : ∃ c:ℝ,∃ v:ℕ,0≤c ∧
    ∀ {n:Side} {P:Rep G n} (X:Coefficient F n) (S:Rules G) {m b R:ℕ}
    (_:10*b<n.val) (live:2*(b+1)<n.val) (_:m*(4*P.p.B+2)+2*P.p.B≤b)
    (he:4*b≤R) (_:X.Format 0 H P) {rent cash:ℝ} (_:0≤rent)
    (u w:poly (links G (0:Site n) b)),
    Summary S P.p b D (fun j:Near (P:=P) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) rent cash u →
    Summary S P.p b D (fun j:Far (P:=P) X m=>X.support j) (fun j=>X.regular j)
      (fun _=>1) rent (expCut P.p m*cash) w →
    coin (trim (unwind (o:=0) live he d (u+w)) (key G d) d) ≤
      cash*rent*c*(1+(b:ℝ))^v*(P.p.threshold+expCut P.p m) := by
  obtain ⟨tests,a,c,v,ha,hc,rank,estimated⟩ := kiosk d D H
  refine ⟨c*a,v,mul_nonneg hc ha,?_⟩
  intro n P X S m b R closed live span he form rent cash hr u w wet dry
  let K:=key G d
  let W (L:poly (links G (0:Site n) b)):=trim (unwind (o:=0) live he d L) K d
  let T:=W (u+w)
  have trims : trim T K d=T := by
    ext i;unfold T W;simp only [trim_coeff];split_ifs <;>simp
  obtain ⟨α,hα,hu⟩:= wet
  obtain ⟨β,hβ,hw⟩:= dry
  have g0:=sumBudget_credit hα
  have nc : coin u ≤ cash*rent := hu.charge.trans (mul_le_mul_of_nonneg_right hα.2.2 hr)
  have fc : coin w ≤ (expCut P.p m*cash)*rent := hw.charge.trans (mul_le_mul_of_nonneg_right hβ.2.2 hr)
  let J:=c*(1+(b:ℝ))^v
  have j0:0≤J:=by dsimp [J];positivity
  have e0:0≤expCut P.p m:=(Real.exp_pos _).le
  let L:=cash*rent*J*(P.p.threshold+expCut P.p m)
  have l0:0≤L:=mul_nonneg (mul_nonneg (mul_nonneg g0 hr) j0) (add_nonneg P.p.threshold_pos.le e0)
  have checks (A:Snap G d) (ok:A∈tests): ‖aeval (kp d A) T‖≤L := by
    have eval (q:poly (links G (0:Site n) b)) : aeval (kp d A) (W q)=evaluate_ray (walked (tacks (o:=(0:Site n)) H live A) q) d := by
      rw [veneer _ live he,ray_stamp]
    have no := null_read X m S closed live span degree form (⟨α,hα,hu⟩) A
    have a0:= (estimated _ ok _ _ _ live P.p u hu.produced.choose_spec.1.degree).2
    rw [no,zero_sub,norm_neg] at a0
    have b0:= (estimated _ ok _ _ _ live P.p w hw.produced.choose_spec.1.degree).1
    have h1: ‖aeval (kp d A) (W u)‖ ≤ (cash*rent)*J*P.p.threshold := by
      rw [eval]
      rw [mul_assoc (coin u) c] at a0
      exact a0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right nc j0) P.p.threshold_pos.le)
    have h2: ‖aeval (kp d A) (W w)‖ ≤ ((expCut P.p m*cash)*rent)*J := by
      rw [eval]
      rw [mul_assoc (coin w) c] at b0
      exact b0.trans (mul_le_mul_of_nonneg_right fc j0)
    rw [show T=W u+W w by unfold T W;rw [map_add,LiftMark.trim_add],map_add]
    exact (norm_add_le ..).trans ((add_le_add h1 h2).trans_eq (by unfold L;ring))
  refine (rank T trims L l0 checks).trans_eq ?_
  unfold L J;ring

/-- The Wick contraction is taken before the projection and may change every
lower angular grade, including the constant. Its size has one full covariance
factor after weighting by the physical threshold. -/
private theorem addPrice {Z:Type} (a b:poly Z) :
    coin a ≤ coin b + coin (a-b) := by
  calc
    coin a = coin (b+(a-b)) := congrArg coin (by abel)
    _ ≤ coin b + coin (a-b) := Rise.taller 0 zero_le_one _ _

private theorem cutPrice {Z V:Type} (p:poly V) (w:Z→ℕ) (C:ℝ) (C1:1≤C)
    (f:V→Z→₀ ℂ) (cells:∀ i,cents (glyph (f i)) 0 1≤C) (cap:p.totalDegree≤D) :
    coin (trim (exchange f p) w d)≤coin p*C^D :=
  (trims 1 zero_le_one 0 w d _).trans (rise f 0 zero_le_one C1 cells p cap)

private theorem changePrice {Z V:Type} (p q:poly V) (w:Z→ℕ) (C:ℝ) (C1:1≤C)
    (f:V→Z→₀ ℂ) (cells:∀ i,cents (glyph (f i)) 0 1≤C) (cap:(q-p).totalDegree≤D) :
    coin (trim (exchange f q) w d) ≤ coin (trim (exchange f p) w d) + coin (q-p)*C^D := by
  let a := trim (exchange f q) w d
  let b := trim (exchange f p) w d
  have eq : a-b=trim (exchange f (q-p)) w d := by rw [map_sub,LiftMark.trim_sub]
  have cut := cutPrice (d:=d) (q-p) w C C1 f cells cap
  have z : coin (a-b)≤coin (q-p)*C^D := (congrArg coin eq).le.trans cut
  exact (addPrice a b).trans (add_le_add le_rfl z)

theorem contraction {V Z : Type} (p:poly V) (w:Z→ℕ) (K:Normal.Symmetric V)
    (ε C:ℝ) (ε0:0≤ε) (ε1:ε≤1) (C1:1≤C)
    (cov:∀ i j,‖K.cov i j‖≤ε) (degree:p.totalDegree≤D)
    (f:V→Z→₀ ℂ) (cells:∀ i,cents (glyph (f i)) 0 1≤C) :
    coin (trim (exchange f (milk K p)) w d) ≤ coin (trim (exchange f p) w d) +
      coin p*(ε*(2*(D+2))^D)*C^D := by
  obtain ⟨tail,cap⟩:=bounds K D ε cov ε0 ε1 p degree
  have deg := (MvPolynomial.totalDegree_sub (milk K p) p).trans (max_le cap degree)
  have h := changePrice (d:=d) p (milk K p) w C C1 f cells deg
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right tail (pow_nonneg (zero_le_one.trans C1) D)))

theorem corrected {n:Side} {b R:ℕ} (live:2*(b+1)<n.val) (he:4*b≤R)
    (K:Normal.Symmetric (trimV R G)) (ε C:ℝ) (ε0:0≤ε) (ε1:ε≤1) (C1:1≤C)
    (cov:∀ i j,‖K.cov i j‖≤ε) (q:poly (links G (0:Site n) b))
    (degree:q.totalDegree≤D) (cells:∀ i,cents (glyph (ink d (Subtype.val:trimV R G→Beamer.Address G) i)) 0 1≤C) :
    let f:=ink d (Subtype.val:trimV R G→Beamer.Address G)
    let p:=rename (calls he) (dustAt live q)
    coin (trim (exchange f (milk K p)) (key G d) d) ≤
      coin (trim (unwind (o:=0) live he d q) (key G d) d) +
      coin p*(ε*(2*(D+2))^D)*C^D := by
  intro f p
  have hd:p.totalDegree≤D:=(totalDegree_rename_le ..).trans ((ascent _ _).trans degree)
  exact contraction p (key G d) K ε C ε0 ε1 C1 cov hd f cells

end YM.Integration.WilsonThermometerWeakWick
end
