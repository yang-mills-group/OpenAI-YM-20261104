import YM.RemainderComparison.Passion.Fume
import YM.Next.WARD_BIN.Alone
/-!
# Logical singleton projection on the marker-conditioned expression

Keeper runs after Passion.Both. tilts. Literal `Source.Coefficient` in the actual header and kernel conventions. Keeps `ζ` operator tests normalized before bases, connects X to Pet.R and bound. Before conversion on different bases by RG04, use representation supplying THESE commitments. No assumption chosen χ in Region matches a final stable graph.Via β conversion eventual.Se.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Fallow
open Function Filter Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker Finset
open Solos Mosaic Verse Serif Flues WickReps Ethereal Jolt Lacuna Lobby Passion GridRenewal.Rain PhysicalNext.Repeat WardBin.Crest
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {α:Type*}{G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
variable [Fintype θ][DecidableEq θ](J:Census θ)
abbrev atZ (x :Poly J): ℂ:= x.part J.quiet

def stroke (i:θ): Poly J→L[ℂ] ℂ := Poly.get (J.fire i)
variable (i:θ)
local notation "m"=> stroke J i
lemma blaze (x:Poly J) (hx:x.part J.quiet=0) : (cyclone x).part J.quiet=1 ∧ m (cyclone x)=m x:=by
    rw [passes x hx]; refine ⟨Poly.pass_part _ hx,?_⟩
    change Poly.part (Poly.pass x) (J.fire i)=x.part (J.fire i)
    have hx₀:0<Fintype.card θ:=Fintype.card_pos_iff.mpr ⟨i⟩
    unfold Poly.pass; rw [Poly.part_sum,sum_eq_single 1]; simp
    · intro n hn he; rcases Nat.eq_zero_or_pos n with h|h
      · subst n; simp [J.fire_hot i]
      have h: (J.fire i).val.card<n:=by unfold Census.fire; simp; omega
      rw [Poly.part_smul, Poly.high x hx _ _ h,mul_zero]
    simp [hx₀]
variable (H:Yard ι α G n)(a b:α)(U:Config G n) (z:ι→Poly J) {D:ι→Finset θ}{q:θ→ℝ}{x B':ℝ}{k:ℕ}
variable (h:Passion.Oriented D J Z z)(hv:Rep G n)(hr:hv.activities.forced=H.more)(hf:hv.activities.K=Ethereal.dusk H Z b)(ho:Jolt.Orbit H Z)
local notation "A"=>hv.activities
include h hf ho
omit [Fintype θ] in
lemma hush (j:ℕ) : Poly.part (H.song Z z a U j) J.quiet=(Complex.ofReal ((A).K j U)):=by
    by_cases ht:Jolt.phase H Z j
    · have hL:= Flues.cold Z z (H.score j) ht -- find
      unfold Yard.song; rw [Poly.part_smul,hL,hf,dusk, if_pos ht, ho.quiet j ht a b]; simp
    unfold Yard.song; rw [Poly.part_smul,hf, dusk, if_neg ht,Passion.positive h _ ht]; simp
include hr
variable (hx:hv.p=p)
include hx
omit [Fintype θ] in
lemma serene (p':Finset ℕ): (Yard.gala H p Z z a U p').part J.quiet= (↑((A).gasOccurrence hv.p p' U) : ℂ):=by
    have hp : (H.manifest a).admissible p U p'=(A).admissible hv.p U p':=by unfold Yard.manifest Activities.admissible; rw [hx,hr]
    unfold Yard.gala Merge.Photo.fronts; rw [hp]; split_ifs; next hh=>
       simp_rw [quiet_prod',hush Z J H a b U z h hv hf ho,Activities.gasOccurrence,if_pos hh,Complex.ofReal_prod]
    next hh=> simp [Activities.gasOccurrence,hh]
omit h hf ho hr hx in
def scoreP (f:ℕ) (U:Config G n):ℂ:= ((H.song Z z a U) f).part (J.fire i)
omit [Fintype θ] in
lemma bolder {d:ℕ}{F:Labels.Frame G d}(M:Coefficient F n)(hG:M.forced=scoreP Z J i H a z) (b':Finset ℕ) :
    Poly.part (Yard.gala H p Z z a U b') (J.fire i)=M.marked hv b' U:=by
    have hp : (H.manifest a).admissible p U b'=(A).admissible hv.p U b':=by unfold Yard.manifest Activities.admissible; rw [hx,hr]
    unfold Yard.gala Merge.Photo.fronts Coefficient.marked; rw [hp]; split_ifs
    · rw [fire_prod,hG]; simp_rw [hush Z J H a b U z h hv hf ho]; rfl
    rfl
-- no projection of density needed to compute header.C.Applies from PHY world
lemma veil {d:ℕ}{F:Labels.Frame G d}(P:Source.Coefficient F n)(s:Site n)(C:SectionData F) (hG:P.forced=scoreP Z J i H a z) (b':Marker.Poly J)(hB:b'.part J.quiet=0) (he:P.exponentialEntry s C hv U= b'.part (J.fire i)) (hK:Summable (H.gala p Z z a U)) : let V:= (Complex.ofReal (Real.exp (hv.exponent U))) • ((cyclone b')*(∑' j,H.gala p Z z a U j))
    V.part J.quiet=(↑(hv.eval U):ℂ) ∧ V.part (J.fire i)=P.density s C hv U:=by
   intro V; have hh:= hK; let f (j:Finset ℕ):=H.gala p Z z a U j
   obtain ⟨hP,hP'⟩:=blaze J i b' hB
   change (cyclone b').part (J.fire i)=b'.part (J.fire i) at hP'
   have hb:(∑' j,f j).part J.quiet= (↑((A).gas hv.p U):ℂ):=by rw [Poly.share hK]; unfold Activities.gas; rw [Complex.ofReal_tsum]; apply tsum_congr; exact serene p Z J H a b U z h hv hr hf ho hx
   have hm:(∑' j,f j).part (J.fire i)=∑' j,P.marked hv j U:=by rw [Poly.share hK]; exact tsum_congr fun i'=> bolder p Z J i H a b U z h hv hr hf ho hx P hG i'
   unfold V; rw [Poly.part_smul,Poly.part_smul,fire_mul, Poly.quiet_mul]; -- rw hquiet after
   unfold f at hb hm; rw [hP,hP',hb,hm] -- edit hp typo, Coee
   unfold Coefficient.density; rw [he]; unfold Rep.eval; rw [Complex.ofReal_mul]; constructor<;> ring
end YM.RemainderComparison.Fallow
