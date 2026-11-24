import YM.GapsContact.Slab.Dyadic
import YM.GapsContact.Focus
/-!
# Short slab across all sufficiently small physical lengths

Same reconstruction data as EveryPhase. No need to change Final or Kernel when choosing the
length etc. Can include finite-order Trace.FieldComparison calibration on exactly those choices (via
PhaseTrace consumer, doesn't assert general RG conclusions). Insertion prices **proved** in
unselected and any character chamber for arbitrary normalized finite degree fields: e.g.
cost≤1 is sufficient; cost budgets for frames/couplings to be exhibited separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Ascent
open Function Filter Set Extraction Table Climb Spec MeasureTheory Trace Trace.Pilot
open Trace.Terrace Trace.Over Next.UVStress MergeProof.East
open OS Boundary EveryPhase
open scoped Topology BigOperators InnerProductSpace Classical NNReal ContDiff
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {d : ℕ}
variable (F : Final C f S) (hG:G.Simple)
variable {H:(Climb.Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}
variable (X: Bliss F 𝓛 Z H)

local notation "I"=> Work.C01.single F.α.unselected F.room.kernel.laws.toSymmetric
lemma shrink_some {r δ:ℝ}(hr:0<r)(ht:δ ∈ Ioc (0:ℝ) 1)(hL:4 ≤ LogV r) :
    let t:=r*((δ/LogV r)^2); t∈ Ioc 0 r ∧ t* LogV t ≤ r*δ ∧ r/t=(LogV r / δ)^2 := by
  intro t; let k:= LogV r; have hk: 0<k:= lt_of_lt_of_le (by norm_num : (0:ℝ)<4) hL
  obtain ⟨hd,hδ⟩:= ht; have hp:0<t:=by change 0 < r*(δ/k)^2; positivity
  refine ⟨⟨hp, mul_le_of_le_one_right hr.le (pow_le_one₀ (div_nonneg hd.le hk.le) ((div_le_one hk).mpr (hδ.trans (le_trans (by norm_num : (1:ℝ) ≤ 4) hL))))⟩, ?_, ?_⟩
  · have hx:LogV t=k+2*Real.log k+2*Real.log δ⁻¹:=by
      unfold LogV; rw [Real.log_inv]; unfold t; change -Real.log (r*(δ/k)^2)=_
      rw [Real.log_mul hr.ne' (pow_ne_zero 2 (div_pos hd hk).ne'), Real.log_pow,
         Real.log_div hd.ne' hk.ne',Real.log_inv, show k= -Real.log r from Real.log_inv r]; push_cast; ring
    have hc(t:ℝ)(h:1 ≤ t):Real.log t ≤ t:= Real.log_le_self (zero_le_one.trans h)
    have h₁:= hc k ((by norm_num : (1:ℝ) ≤ 4).trans hL)
    have h₂:= hc δ⁻¹ ((one_le_inv₀ hd).2 hδ)
    have hh: δ*(2*Real.log δ⁻¹)≤2:=by
      calc _ ≤ δ*(2*δ⁻¹) := by gcongr
           _ = _ := by field_simp
    have hf: δ* (k+2*Real.log k) ≤ 3*k := (mul_le_mul_of_nonneg_left (by linarith only [h₁] : k+2*Real.log k ≤ 3*k) hd.le).trans (mul_le_of_le_one_left (by positivity) hδ)
    have hQ: δ*LogV t ≤ k^2:=by
      rw [hx,mul_add]; change 4≤k at hL; nlinarith only [hL,hh,hf]
    change r*(δ/k)^2 * _ ≤ _; rw[mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ hr.le
    rw [div_pow,div_mul_eq_mul_div, div_le_iff₀ (pow_pos hk _)]
    rw [sq, mul_assoc]; gcongr
  change r/(r*(δ/k)^2)=(k/δ)^2; field_simp

lemma own_pay {A R:ℝ} {m:ℕ} (h:Billing F R d A m) (hA:1 ≤ A) {r δ:ℝ} (hr:r∈ Ioc 0 R) (ht:δ∈ Ioc 0 1)
    (hL:4 ≤ LogV r) (p:ℝ≥0) (hp:0<p)(h₀:r*δ ≤ p) (x:S.Field d):
    ‖I hp d x‖ ≤ A^2 * (LogV r / δ)^(2*m) * cost F d r x := by
  let t:=r * (δ / LogV r)^2; obtain ⟨hs,hK,hx⟩ := shrink_some hr.1 ht hL
  refine ((h.octave t ⟨hs.1,hs.2.trans hr.2⟩).before p hp (hK.trans h₀) x).trans ?_
  refine (mul_le_mul_of_nonneg_left (h.all t r hr hs x) (zero_le_one.trans hA)).trans_eq ?_
  rw [show r/t=(LogV r/δ)^2 from hx,pow_mul]; ring

/-- Uniform continuation-side bundle of choices pasted to the common `Contour`s. -/
abbrev Survey := Option F.α.space.X

variable {F}

def Survey.table (p:Survey F) := p.elim S (fun i=>F.α.ensemble i)
namespace Survey
variable (L : Almanac F)

-- `Survey` is an abbrev; use `Survey.table` explicitly (dot notation might not elaborate)
def chamber (p:Survey F) : Chamber (Survey.table p) timeAxis := by
  cases p with
  | none => exact F.α.room
  | some i => exact L.chambers i

def spread (p:Survey F) : Spread (chamber L p) := by
  cases p with
  | none => exact F.α.unselected
  | some i=> exact L.spreads i

def reads (p:Survey F) : Contour S := p.elim F.B (fun i=>L.contours i)
lemma pantry (p:Survey F) : Bid.Pantry S (table p) _ F.sector.derivatives (spread L p) := by
  cases p with
  | some i=> exact L.pantries i
  | none => exact ⟨F.room.kernel,F.room.kernel,fun _=> le_rfl,F.phase.transport.injection,F.phase.transport.injection,
       F.phase.transport.derivatives,F.phase.phase.lengths⟩
lemma fits (p:Survey F) : Next.BOUNDARY.Compatible S (spread L p) F.sector F.action.spin F.room.kernel.spin (reads L p) := by
  cases p with
  | some i=> exact L.cards i
  | none => exact (Next.BOUNDARY.onFinal F).1
lemma uniform (p:Survey F) (s:ℝ≥0) (hs:0<s) (d:ℕ) (v:S.Field d) :
    ‖Work.C01.single (spread L p) (pantry L p).adopted.laws.toSymmetric hs d v‖ ≤ ‖I hs d v‖ := by
  cases p with
  | none => exact le_rfl
  | some i=> exact L.priced i (s+s) _ (Work.C01.centeredSlab _ _ hs)
end Survey
variable (F)

-- cost of time-ordered gap can be paid as (LogV r)^D times INVERSE SCALED gap to D
structure OpenSky (d:ℕ)(R:ℝ)(A:ℝ)(m:ℕ) : Prop where
  archive : Billing F R d A m
  duration : ∀ r∈ Ioc 0 R, 4 ≤ LogV r
  radius (L : Almanac F) (i: Survey F) (B: Small S (Survey.chamber L i)) : B.concretized (Survey.spread L i) →
      ∀ r∈ Ioc 0 R, ∀ δ∈ Ioc (0:ℝ) 1, ∀ p:ℝ≥0, 0<p→ r*δ ≤ p→ ∀ v:S.Field d,
        ‖B.bar p (S.pin d v)‖ ≤ A^2 * (LogV r / δ)^(2*m) * cost F d r v

include X hG
lemma opened_sky (d:ℕ) : ∃ (R:ℝ) (A:ℝ) (m:ℕ),0<R ∧ 1≤A ∧ OpenSky F d R A m := by
  obtain ⟨R,A,m,hR,hA,h⟩ := bills F hG X d
  obtain ⟨r,hr,hx⟩ := bounded_all ((show Tendsto LogV trail atTop from Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).eventually_gt_atTop (4:ℝ))
  let s:= min r R
  have hm(t:ℝ)(ht:t∈ Ioc 0 s): t∈ Ioc 0 R ∧ 4 ≤ LogV t:= ⟨⟨ht.1,ht.2.trans (min_le_right ..)⟩,(hx _ ⟨ht.1,ht.2.trans (min_le_left ..)⟩).le⟩
  refine ⟨s,A,m,lt_min hr hR,hA,⟨⟨fun t ht=>h.octave t (hm t ht).1,fun u t ht => h.all u t (hm t ht).1⟩, fun t ht=> (hm t ht).2, ?_⟩⟩
  intro L i B hB t ht δ hδ p hp h₁ v
  rw [small_field B hB (Survey.pantry L i).adopted.laws.toSymmetric hp v]; exact (Survey.uniform L i p hp d v).trans (own_pay F h hA (hm t ht).1 hδ (hm t ht).2 p hp h₁ v)
end YM.GapsContact.Ascent
