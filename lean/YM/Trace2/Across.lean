import YM.Trace2.Transfer
import YM.Trace.NoFock
import YM.Trace.TargetSpectral

set_option autoImplicit false
noncomputable section
namespace YM.Trace
open Function Filter Set OS Maxwell Labels Table Spec OPE
open scoped Topology ContDiff BigOperators RealInnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (F:Final C f S)

/-- Inhabited by the all-character construction. Retains one common contour choice per character. -/
structure Diplomacy (F : Final C f S) where
  book : EveryPhase.Almanac F
  proof' : EveryPhase.Completed F book
lemma diplomacy_exists : Nonempty (Diplomacy F):= by obtain ⟨L,h⟩:=EveryPhase.all_characters F; exact ⟨L,h⟩
variable {F} (D:Diplomacy F)

def selectionView (i:F.α.space.X) : OS.Selection S := {F.α with atPoint:=i,leaps:=D.book.chambers i,slabs:=D.book.spreads i}
/-- Re-index only the distinguished phase. Family, table, sector, ensemble, exact observables,
unselected space, calibration and extraction are literally retained. Uses vacuum uniqueness and
continuations proved in the same every-character construction, not `Final` from another trajectory. -/
def Diplomacy.onCharacter (i:F.α.space.X) : Final C f S := {
  F with
  α:=selectionView D i, phase:=⟨F.phase.transport,
      ⟨F.phase.phase.lengths,F.phase.phase.still,F.phase.phase.decomposition,F.phase.phase.chosen,
       F.phase.phase.states,F.phase.phase.sym,F.phase.phase.retains,F.phase.phase.coordinates,
       F.phase.phase.calculus,F.phase.phase.flux,(D.book.pantries i).counter,D.proof'.euclid i⟩⟩,
  A:=D.book.contours i, action:= D.book.actors i,
  realization:= {F.realization with chosen:= (D.book.cards i).fromPhase, qt:=D.proof'.isTheory i} }
lemma centered_at (i:F.α.space.X) : massCenter F (some i) = meanExact (D.onCharacter i) := by rw [massCenter,meanExact, onept_eq]; rfl
lemma centered_distinguished : massCenter F (some F.α.atPoint) = meanExact F:= by rw [massCenter,meanExact,onept_eq];rfl

def separated (s:ℝ) :=points (![(0:E4),s • basis timeAxis])
lemma restTrace_phase (s e:ℝ) : restTrace F e s=traceEta F (some F.α.atPoint) (separated s) e e:= by unfold restTrace traceEta useAt;congr 1; ext1 i;fin_cases i <;> simp [theta,withoutMean]
lemma restTrace_chosen (i:F.α.space.X)(s:ℝ):
    restTrace (D.onCharacter i) (meanExact (D.onCharacter i)) s=central F (some i) (separated s):= by rw [restTrace_phase,central,centered_at D];rfl
lemma restTrace_origin (s:ℝ):restTrace F (meanExact F) s=central F (some F.α.atPoint) (separated s):= by rw [restTrace_phase,central,centered_distinguished]
lemma basis_time_bound : ‖basis timeAxis‖=1:=by
  unfold basis
  change ‖PiLp.single 2 (β:=fun _=>ℝ) timeAxis 1‖=1
  rw [PiLp.norm_single]; norm_num
lemma room_separated (s:ℝ)(hs : s≥0):WithinRoom s 1 1 (separated s).ofLp 0:=by
  constructor
  · intro i; fin_cases i <;> simp [norm_smul,separated,points,Real.norm_eq_abs, abs_of_nonneg hs,hs]
  intro i j he; fin_cases i <;> fin_cases j <;> norm_num [norm_smul,separated,points,WithLp.equiv_symm_apply,Real.norm_eq_abs,abs_of_nonneg hs,basis_time_bound] at *

lemma loglaw_at (H:Services C f S) (i:F.α.space.X){a:ℝ}(ha : LogLaw F a): LogLaw (D.onCharacter i) a := by
    unfold LogLaw at ha ⊢
    have hf:=((log_agreement F H) 1 1)
    have hx: Tendsto (fun R:ℝ=>(logWeight R:ℂ)*(central F (some i) (separated R⁻¹)-central F (some F.α.atPoint) (separated R⁻¹))) atTop (𝓝 0):= by
      apply Metric.tendsto_nhds.mpr; intro ε hε
      filter_upwards [eventually_gt_atTop (0:ℝ), tendsto_inv_atTop_nhdsGT_zero.eventually (hf ε hε zero_le_one zero_lt_one)] with R hr H
      rw [dist_zero_right,← Complex.real_smul]; simpa [logWeight, Real.log_inv, inv_pow] using H _ _ (room_separated R⁻¹ (inv_pos.mpr hr).le) (some i) (some F.α.atPoint)
    have hx:=hx.add ha; rw [zero_add] at hx; exact hx.congr (fun R=> by rw [restTrace_origin,restTrace_chosen,mul_sub,sub_add_cancel])

/-- Tested trace estimate with one and the same subsequence of UV lengths,
even varying the phase arbitrarily at each length. No log precision asserted. -/
lemma engineering_retreat (H:Services C f S) (E:Echo C f S) : ∀ v:ℕ→Viewers E.final,
    Tendsto (fun i=> (E.path.r (E.along i))^8 • central E.final (v i) (separated (E.path.r (E.along i)))) atTop (𝓝 0) := by
   intro v; let A:=E.final;let a:= A.α.atPoint
   let r:= E.path.r ∘ E.along; have hr : Tendsto r atTop (𝓝[>]0):=tendsto_nhdsWithin_iff.mpr ⟨E.path.drips.comp E.rate.tendsto_atTop,Eventually.of_forall fun i=> E.path.positive _⟩
   let error (i):ℝ:=2*(cape A)^2+2*(r i)^(-(7.5:ℝ))
   have hz : Tendsto (fun i=> ((r i)^8 : ℝ)*error i) atTop (𝓝 0):= by -- exponent Nat
      have hu := (Tendsto.comp (continuousAt_id.tendsto.pow 8 : Tendsto (fun r:ℝ=>r^8) (𝓝 0) _) (tendsto_nhds_of_tendsto_nhdsWithin hr)).mul_const (2*(cape A)^2)
      have ht := ((Real.continuous_rpow_const (show (0:ℝ)≤0.5 by norm_num)).continuousAt.tendsto.comp (tendsto_nhds_of_tendsto_nhdsWithin hr)).mul_const 2
      have he:=hu.add ht; dsimp only [id_eq,Function.comp_apply] at he; rw [zero_pow (by omega : 8≠0),zero_mul,Real.zero_rpow (by norm_num : (0.5:ℝ)≠0),zero_mul,zero_add] at he
      apply he.congr; intro i; change _+r i^(_ : ℝ)*_=_; dsimp only [error];rw [show (0.5:ℝ)=8 + -7.5 by norm_num,Real.rpow_add (show 0<r i from E.path.positive _),Real.rpow_ofNat]
      change (r i)^8*(_)+_= _; ring
   let c (a':Viewers A) i:=central A a' (separated (r i))
   have hx : Tendsto (fun i=> (r i)^8 • (c (v i) i - c (some a) i)) atTop (𝓝 0):= squeeze_zero_norm' (?_) hz
   case refine_1=>
    filter_upwards [hr.eventually (centered_phased A H (M:=1) (ε:=0.5) (η:=1) zero_le_one (show (0:ℝ)<0.5 by norm_num) zero_lt_one)] with i he
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos (show 0<r i from E.path.positive (E.along i)) 8)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (E.path.positive _ |>.le) _)
    apply (he _ _ (room_separated _ (E.path.positive _ |>.le)) _ _).trans_eq; norm_num [error]
   have hm:=hx.add (E.retreats (meanExact E.final));rw [zero_add] at hm
   apply hm.congr; intro i; dsimp only [c]; rw [show central A (some a) (separated (r i)) = _ from (restTrace_origin (F:=A) _).symm]; simp only [smul_sub, Complex.real_smul]
   push_cast; exact sub_add_cancel _ _
end YM.Trace
