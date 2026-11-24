import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Marker
/-! # G.4/6 phase extension also on single-scale compacts, prior to the inverse.
Use real `Allowance` on same log windows and full argument positions. No separated-phase products. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe Flash259HorizonFork ScaleCost
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)
variable {I J:Type}[Fintype I]{l:Filter J}{r:J→ℝ} (hr:Tendsto r l late) (o:J→E4)
    {x:J→ I→E4} {d:I→ℕ}{u:J→(i:I)→Sec G (d i)}
    (hu:∀ (i:I) (b:Toon G (d i)),Allowance l r (fun _=>1) (fun j=>coord b (u j i)))
    {M δ:ℝ}(hM:0≤M)(hδ:0<δ)(hx:∀ᶠ i in l,WithinRoom 1 M δ (x i) 0)
local notation "col" => (enter Z)

lemma zero_far (T:Table C.book) (w: I→E4) (h:T.Hierarchy) (u:Labels S d) (f : Fin 0→E4) {e:Fin 0→ℕ} (v:Labels S e) (hk:Injective w) :
    whole T w u f v = moment T w u := by
  rw [whole_observed, Orbits.observed]; apply Eq.trans ?_ (perm_observe T h.laws.toSymmetric (Equiv.sumEmpty I (Fin 0)) _ hk); congr 1 <;> (funext i; cases i; rfl; exact Fin.elim0 ‹Fin 0›)
include H hZ hq hQ hM hδ hr hx hu
lemma covering (p q : J → Viewers F) : Allowance l r r (fun i=> moment (spectator F (p i)) (atPosition (o i) (r i) (x i)) (col (r i) (u i))-
    moment (spectator F (q i)) (atPosition (o i) (r i) (x i)) (col (r i) (u i))) := by
  let A:= max 1 (M/δ); let s i:= A*r i
  let y:=fun (_:J)=> (Fin.elim0:Fin 0→E4); let e:=fun (_:Fin 0)=>0
  have h : 1≤A := le_max_left ..; have hp:= zero_lt_one.trans_le h
  have hs:Tendsto s l late := by
    rw [tendsto_nhdsWithin_iff]; constructor
    · simpa only [mul_zero] using ((tendsto_nhdsWithin_iff.mp hr).1.const_mul A)
    exact (hr.eventually self_mem_nhdsWithin).mono fun i h=> mul_pos hp h
  have he : ∀ᶠ i in l, Flash259HorizonFork.Ready (r i) (s i) M δ (x i) (y i) := by
    filter_upwards [hx,hr.eventually self_mem_nhdsWithin] with i x hr; constructor
    · exact hr
    · exact le_mul_of_one_le_left hr.le h
    · simpa using x.span
    · intro j; exact j.elim0
    · intro j; exact j.elim0
    · simpa using x.spaced
    · intro j; exact j.elim0
    unfold s; have e : M ≤ A*δ := (div_le_iff₀ hδ).mp (le_max_right ..); rw [mul_comm A, mul_assoc]; exact mul_le_mul_of_nonneg_left e hr.le
  refine ((split_phase (v:=fun (_:J) (_:Fin 0)=> leaf G 0) (e:=e) F Z Q H hZ hq hQ hs (o:=o) hM hδ he hu (fun j=> j.elim0) p q).congr ?_).transport ((isBigO_refl r l).const_mul_left A)
  filter_upwards [he] with i h; have hi := (beside_distinct.mp (profiles (o i) h hδ)).1; rw [zero_far (spectator F (p i)) _ (spectate ..) _ _ _ hi,zero_far (spectator F (q i)) _ (spectate ..) _ _ _ hi]

omit H hZ hq hQ hu hM hδ hx
include sim hr
lemma flat {E : Type*} [NormedAddCommGroup E]{f:J→E} (w:ℕ) (p : Allowance l r r f) : f=O[l] fun i=>g0 G (r i)^w := by
  have hs := (pace sim).comp hr; let g i:= g0 G (r i)
  have z : (g ∘ id)=g := rfl
  obtain ⟨k,A⟩:= p
  have B : (fun i=>OPE.Log.badge (r i) ^ k)=O[l] (fun i=> g i ^ (-2*(k:ℝ))) := by
    have h' : (fun i=>OPE.Log.badge (r i))=O[l] (fun i=>g i ^ (-(2:ℝ))) := by
      refine IsBigO.of_bound (2 * G.slopeConstant⁻¹) ?_
      filter_upwards [log_pays hr,hr.eventually (adjustment sim), hr.eventually (holds_cash.eventually_ge_atTop 1),now hs] with i h A d hi
      have b: OPE.Log.badge (r i)=1+cash (r i):=by rw [OPE.Log.badge,OPE.run,cash,Real.log_inv]
      have hi : 0 < g i := hi
      rw [ Real.norm_of_nonneg (zero_le_one.trans h), Real.norm_of_nonneg (by positivity), b, Real.rpow_neg (by positivity), Real.rpow_two,← inv_pow ]
      rw [A] at d ⊢; change _ ≤ 2*_* ((g0 G (r i))⁻¹)^2; linarith
    refine (h'.pow _).congr' (EventuallyEq.refl ..) ?_
    filter_upwards [now hs] with i h; have hi:0<g i:=h; rw [Real.rpow_mul hi.le, Real.rpow_natCast]
  refine (A.trans (((length sim ((w:ℝ)+2*(k:ℝ))).comp_tendsto hr).mul B)).congr' (EventuallyEq.refl ..) ?_
  filter_upwards [now hs] with i h; dsimp only [Function.comp_apply,g]; rw [ ← Real.rpow_add (show 0 < g0 G (r i) from h), show ((w:ℝ)+ 2*(k:ℝ)+ -(2:ℝ)*(k:ℝ))=(w:ℝ) by ring, Real.rpow_natCast]
end YM.FVA2.GradedFar259.Original
