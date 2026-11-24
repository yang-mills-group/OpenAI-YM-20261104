import YM.SharpGram.Lenses.Sights
import YM.OS.Core
set_option maxHeartbeats 500000
/-!
# The actual point-reflected two-point form in log lengths

The time-axis point detector. Linear in the FIRST label, antilinear in second,
for consistency with Free.Pair. Includes literal connection to OS using the
second label of our detector as the earlier reflection slot in the future
Hilbert proof. Use monotonicity for decreasing length. Thus intermediate
points between integer log steps needn't pay a separate price, and there is
no assertion of comparability of actual tilt with actual selfadjoint Gram
without estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Annulus
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open PhysicalNext.RankCovariance Org Spec Next.UVStress Further.CorrectedLift MergeProof.East
open Lenses OS Word Push.FiniteDetection.Free Weak.Portfolio
open scoped Topology ContDiff BigOperators Classical NNReal InnerProductSpace
set_option quotPrecheck false
variable {G:Gauge}{L:Register G}{S:Table L}

abbrev form {G:Gauge}{L:Register G} (S:Table L)(h:S.RealSpin)(d:ℕ)(r:ℝ):= glass S h d (r • detectors)
def positiveForm {G:Gauge}{L:Register G} (S:Table L)(h:S.RealSpin)(d:ℕ)(r:ℝ) : Prop :=
  ∀ x ≠ 0, 0 < form S h d r x x
variable (H : S.Hierarchy) {t : ℕ}
variable {r:ℝ}

-- proper OS ordering: right ray in slot0, left reflected of slot1.
def sourceWord (x:L.Ref t)(hr:0<r) : OS.Future L timeAxis:=
  ⟨[((r/2) • basis timeAxis, (⟨t,x⟩:L.Token))],by
    constructor
    · exact Word.locations.mpr (by simp)
    intro v hv; rw [show v= _ from List.mem_singleton.mp hv]; simp; exact hr⟩
lemma detector_in (hr : 0<r) : r • detectors ∈ conf 2 := (Next.UVStress.enlarged hr _).mp detectors_in
lemma unfolded (X : OS.Chamber S timeAxis) (hr:0<r) (x y : L.Ref t) :
    S.classMoment S (fun _=>t) (r • detectors) ![S.project t x, S.adj H.spin t timeAxis (S.project t y)] =
      inner ℂ (X.GNS.plant (sourceWord y hr)) (X.GNS.plant (sourceWord x hr)) := by
  let p : Points 2 := r • detectors
  let u := (r/2) • basis timeAxis
  let v := Ortho.move (Signed.reflect timeAxis) u
  let w (y:L.Ref t) :=sourceWord y hr
  let ix : L.Token := ⟨t,x⟩; let iy : L.Token := L.reflectedToken timeAxis ⟨t,y⟩
  let q : Fin 2 → L.Token := fun i=>(⟨t,(![x,L.adj t timeAxis y] : Fin 2→ L.Ref t) i⟩:L.Token)
  rw [X.GNS.measure]
  change _ = S.expect (Word.reflect _ _ ++ _)
  let P := Word.reflect (sourceWord y hr).val timeAxis ++ (sourceWord x hr).val
  have hP : P = [(v,iy),(u,ix)] := by simp [P,v,iy,u,ix,sourceWord,Word.reflectedPoint]
  have hx : Word.distinct P := Word.twoSides (sourceWord y hr).property (sourceWord x hr).property
  have hv : v = -u := by
    unfold u v; ext i; by_cases h:i=timeAxis <;> simp [h,u]
  have hu : u+u=r • basis timeAxis:= by unfold u; rw [← add_smul]; ring_nf
  have he:P.reverse = [(u,ix),(v,iy)] := by rw [hP]; rfl
  have hy: Word.carry P.reverse u=Word.realize q p:=by
    rw [he]; let A : L.Token := ⟨t,L.adj t timeAxis y⟩; have hA: A=iy:=rfl
    simp [p,q,v,detectors,Word.carry,Word.realize,hu,hv,←hA,A, List.ofFn_succ, ix]; rfl -- adjust
  change _=S.expect P
  rw [← Table.order S H.laws.toSymmetric hx (List.reverse_perm P).symm,
      ← OS.invariance H.translations (show Word.distinct P.reverse from Word.locations.mpr (by rw [List.map_reverse,List.nodup_reverse]; exact Word.locations.mp hx)) u,
      hy,S.readAt]
  · rw [adj_project]; let a : Fin 2 → L.Ref t := ![x,L.adj t timeAxis y]; change S.classMoment S _ _ _=S.read p q
    rw [show ![_, S.project t (L.adj t timeAxis y)]=fun i : Fin 2=> S.project t (a i) from funext (fun i=>by fin_cases i <;> rfl)]
    exact S.class_agrees S H.laws.toSymmetric (fun _=>le_rfl) _ (detector_in hr) a

lemma energy (X : OS.Chamber S timeAxis)(hr:0<r)(x y : S.Field t) :
   form S H.spin t r x y= (inner ℂ (X.GNS.plant (sourceWord (S.representative t y) hr)) (X.GNS.plant (sourceWord (S.representative t x) hr))).re:= by
    rw [← unfolded H, glass_reads,S.rep,S.rep]
lemma symmetric (hr:0<r)(x y:S.Field t): form S H.spin t r x y=form S H.spin t r y x := by
   obtain ⟨X⟩:= OS.realization H timeAxis
   rw [energy H X hr, energy H X hr]; exact inner_re_symm (𝕜:=ℂ) ..
lemma positive (hr:0<r)(x:S.Field t): 0≤ form S H.spin t r x x:=by obtain ⟨X⟩:= OS.realization H timeAxis; rw [energy H X hr]; exact inner_self_nonneg (𝕜:=ℂ) (x:=X.GNS.plant (sourceWord (S.representative t x) hr))
lemma energy_sq (X : OS.Chamber S timeAxis)(hr:0<r)(x : S.Field t) :
   form S H.spin t r x x= ‖X.GNS.plant (sourceWord (S.representative t x) hr)‖ ^ 2 := (energy H X hr ..).trans (_root_.inner_self_eq_norm_sq (𝕜:=ℂ) (X.GNS.plant (sourceWord (S.representative t x) hr)))

lemma prolongs {s:ℝ} (hr:0<r)(hs:r ≤ s) (a:L.Ref t) : sourceWord a (hr.trans_le hs) =
       OS.travel (sourceWord a hr) ⟨(s-r)/2,div_nonneg (sub_nonneg.mpr hs) zero_le_two⟩ := by
    apply Subtype.ext; unfold OS.travel
    simp only [sourceWord, Word.carry,List.map_cons,List.map_nil]; rw [← add_smul]; change _ = [((r / 2+(s-r)/2) • basis timeAxis, (⟨t,a⟩: L.Token))]; rw [show r / 2+(s-r)/2=s/2 by ring]

/-- Monotone all intermediate lengths; no loss multiplying costs across neglected gaps. -/
lemma expands (t : ℕ)(x : S.Field t)(r s : ℝ)(hr : 0<r)(hs:r ≤ s):
    form S H.spin t s x x ≤ form S H.spin t r x x := by
   obtain ⟨X⟩:= OS.realization H timeAxis
   rw [energy_sq H X (hr.trans_le hs),energy_sq H X hr,prolongs hr hs,X.atBirth]
   exact pow_le_pow_left₀ (norm_nonneg _) (((X.flow.E _).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (X.flow.shrinks _))) _

local notation "x0"=> r • detectors
lemma inherit (P:DiffPlan S)(hP:P.Inclusions S)(h:P.Orientation H.spin) (hr:0<r) {d e:ℕ} (hd:d≤e) (x y:S.Field d):
   form S H.spin d r x y=form S H.spin e r (P.rise hd x) (P.rise hd y):=by
    rw [glass_reads,glass_reads,← Weak.Portfolio.readSecond,←Weak.Portfolio.readSecond]
    rw [Weak.Portfolio.ascend S P hP _ _ (detector_in hr), Weak.Portfolio.firstProbe_read,Weak.Portfolio.firstProbe_read]
    have he : S.adj H.spin e timeAxis (P.rise hd y)= P.rise hd (S.adj H.spin d timeAxis y) := by simp [Table.adj,h.realInc,h.mirrorInc]
    let p : Equiv.Perm (Fin 2):= Equiv.swap 0 1
    have hp (x y:S.Tag): ![x,y] ∘ p=![y,x] := by funext i; fin_cases i <;> simp [p]
    rw [he,← Table.class_perm S S H.laws.toSymmetric p (detector_in hr), hp,
      ← Table.class_perm S S H.laws.toSymmetric p (detector_in hr) ![⟨d,x⟩,(⟨e,P.rise hd (S.adj H.spin d timeAxis y)⟩: S.Tag)],hp]
    apply congr_arg
    exact (hP.kernels hd _ (Points.rearrange_in p (detector_in hr)) ![⟨d,x⟩]).symm

section
variable {C:Family G}{S:Table C.book}{f:Extraction.Order}{u:Filter (ℕ×ℕ)} (F:Final C f S) (B:Lenses.Mantle F u)
include B in
lemma strictSmall (d:ℕ) : ∃ r:ℝ,0<r ∧ ∀ s:ℝ,0<s→s≤r→positiveForm S F.room.kernel.spin d s := by
    obtain ⟨δ,hp,hA⟩:=B.reflects d
    obtain ⟨k,_,hF⟩:=hA.exists
    refine ⟨B.radius k,B.positive _,fun r hr ht x hx=> lt_of_lt_of_le ?_ (expands F.room.kernel d x _ _ hr ht)⟩
    obtain ⟨y,rfl⟩:=(B.lens k d).surjective x
    have he : y ≠ 0 := by intro h; rw [h,map_zero] at hx; exact hx rfl
    specialize hF y; change δ/2 * ‖y‖^2 ≤ form S F.room.kernel.spin d (B.radius k) (B.lens k d y) (B.lens k d y) at hF
    exact lt_of_lt_of_le (mul_pos (half_pos hp) (pow_pos (norm_pos_iff.mpr he) 2)) hF
end
end YM.SharpGram.Annulus
