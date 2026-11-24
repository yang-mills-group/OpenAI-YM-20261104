import YM.RemainderComparison.Fallow.Lyre
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
-- Force masses up front.N.No root drift on merged pol.Stanza from Raise.
variable (i:θ)(F:Plane G n θ)(H:Yard ι α G n)(a:α)(z:ι→ Marker.Poly J)(V:Rep G n)
variable (h:V.activities.forced=H.more) {D:ι→Finset θ}(hZ:H.Sounds V.p R)(hr:Placed R F D) (hp:Passion.Oriented D J Z z)
local notation "rν"=> scoreP Z J i H a z
local notation "F₀"=> F.visor i
set_option quotPrecheck false
local notation "t'"=> (F.visor i).origin
include h hp hZ hr
omit [Fintype θ] in
lemma earned :
    ForceFormat V.p V.activities (F.visor i).origin (scoreP Z J i H a z):=by
    let G x:=(controls Z z (H.score x)).part (J.fire i)
    have he (p:ℕ)(U): scoreP Z J i H a z p U = (↑(H.glow a p U):ℂ)* G p:=Poly.part_smul ..
    have hx:= hZ.families a
    constructor
    · intro j U hv; rw [he] at hv; rw [h]; exact hx.permit j U (fun hh=> left_ne_zero_of_mul hv ((show (H.glow a j U:ℝ)=0 from hh) ▸ rfl))
    · intro j hj; obtain ⟨x,h⟩:∃ U,rν j U≠0:= Classical.byContradiction fun he'=>hj (funext fun U=>Classical.byContradiction fun he=> he' ⟨_,he⟩)
      rw [he] at h
      have hf:=right_ne_zero_of_mul h; have hv:=left_ne_zero_of_mul h
      have hz:i∈ mapWord D (H.score j):= by rw [Passion.pedigree hp i hf]; simp
      obtain ⟨k,hk,hf⟩:= Multiset.mem_bind.mp hz; unfold Local.patch; rw [show V.activities.forced=H.more from (by assumption)]; exact hZ.invested j a k hk x (fun he=>hv (by simp [he])) (hr.legs k i hf)
    · intro j v U; rw [he,he]; rw [show H.glow a j (Lattice.gauge v U)=_ from hx.sym j v U]; rfl
    · intro j U U' hp hW; unfold Local.patch at *; rw [h] at hp hW; rw [he,he]; rw [show H.glow a j U=_ from hx.reads j U U' hp hW]; rfl
    intro j; have hp : rν j= fun U=> (↑(H.glow a j U):ℂ)*G j:=funext (he j)
    rw [hp]; exact ((Complex.continuous_ofReal.measurable.comp (hx.meas j)).mul measurable_const)

variable {q:θ→ℝ}{k:ℕ}(hX:Chorus J q Z z k)(x:ℝ)(hb:Yard.Pays H Z k V.p.B V.p.supportExponent x)
omit [Fintype θ]
include hb hX
lemma purse : ForceCost V.p V.activities rν ((q i)⁻¹ * x):=by
   obtain ⟨f,hf,h,hB⟩:=hb.wages
   have he:= earned R Z J i F H a z V ‹V.activities.forced=_› hZ hr hp
   let w x:= if t'∈H.plane x then (q i)⁻¹*f x else 0
   have hx:0≤(q i)⁻¹:=inv_nonneg.mpr (hX.votes _).le; have hw i:0≤ w i:=by unfold w; split; exact mul_nonneg hx (hf _); exact le_rfl
   refine ⟨w,?_,fun j=> ⟨hw j,fun U=>?_⟩⟩
   · convert budget_scale hx (h t') using 1; funext i; unfold w Local.patch; rw [show V.activities.forced=H.more from ‹_›]; unfold BudgetPoint.mass; split
     · unfold Yard.plane; ring
     rw [mul_zero,mul_zero]
   unfold w; split; next h' =>
       by_cases hX': Verse.load Z (H.score j)≤ k
       · unfold scoreP Yard.song; rw [Poly.part_smul,norm_mul,Complex.norm_real] -- check
         apply le_trans (mul_le_mul (hB _ hX' ..) (Fallow.stroke_bound Z J q hX _) (norm_nonneg _) (hf _)); rw [mul_comm]
       unfold scoreP Yard.song; rw [hX.capacity _ (lt_of_not_ge hX'),smul_zero,Poly.part_nil,norm_zero]; exact mul_nonneg hx (hf _)
   next hx=>
     have hg:rν j=0:=Classical.byContradiction fun hp=> hx (by unfold Yard.plane; rw [← show V.activities.forced=H.more from ‹_›]; exact he.carried _ hp)
     rw [hg]; simp
end YM.RemainderComparison.Fallow
