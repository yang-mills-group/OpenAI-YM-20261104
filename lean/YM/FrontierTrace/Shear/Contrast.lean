import YM.FrontierTrace.Shear.Radial
/-! Tested identity on the finite rays, paying all operator/scaling and suppressing
 unit by unselected subtraction. Reads are point values on separated generic
 directions (can select `tilt` below). Last input costs recorded elsewhere.
 End-point calculus version avoids using stress conservation at coincident points
 or needing remainders for position derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace MeasureTheory Table Climb
open Next.UVStress Work.A01
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval

variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} (F:Spec.Final C f S)
    {r:ℝ} (ℓ:E4)
local notation "L" => YM.FrontierTrace.currentL
local notation "B" => YM.FrontierTrace.currentB
local notation "T" => YM.FrontierTrace.current
local notation "ν" => timeAxis
variable (P : Spin.change S 4)
local notation "A" => scalarA P
local notation "S01" => metric0 C.labels 0 1

lemma radial_generic (hℓ:∀ i:Axis,ℓ i≠0) (s:ℝ)(hs:0<s) : atShape (s • ℓ)∈ generic 2 := by
   rintro i j k ht
   fin_cases j <;> fin_cases k
   · rfl
   · exact False.elim (mul_ne_zero hs.ne' (hℓ i) ht)
   · exact False.elim (mul_ne_zero hs.ne' (hℓ i) ht.symm)
   rfl

def tilt:E4:= WithLp.toLp 2 fun _:Axis=> (1/2:ℝ)
lemma norm_tilt: ‖tilt‖=1 := by
  have he:= real_inner_self_eq_norm_sq tilt
  rw [PiLp.inner_apply,Fin.sum_univ_four] at he
  change (((1/2:ℝ)*(1/2))+1/2*(1/2)+1/2*(1/2)+1/2*(1/2)) = _ at he; nlinarith [norm_nonneg tilt]
lemma tilt_open : ∀ i: Axis, tilt i ≠ 0 := fun _=> by unfold tilt; norm_num

/- Point readout hypotheses later will be on the ray ℓ vs r (positions scaled
  by same variable r). S uses unselected centering; offdiag has no identity.
  Not connected vacuum-continuation data; every piece is offdiagonal.
  ℓ∈unit sphere, t∈[1,2]. Both cutoffs already removed, `Bound` order. -/
def pure (A':S.Field 4)(r t:ℝ) : ℂ:= custom (atShape ((r*t) • ℓ)) A' A'
def KK (r:ℝ):ℝ→ℂ:= YM.FrontierTrace.pure (C:=C) ℓ A r
/-- Moving field convention: test metric0 (`freeStress`) sent by P, and A.
Not assuming P identifies full SO frames. Divide by the geometric factor ℓ0ℓ1,
nonzero; no coupling inverse here. Thus dividing out offaxis reflection sign. -/
def shear (r t:ℝ) : ℂ:= (ℓ 0 * ℓ 1)⁻¹ • custom (atShape ((r*t) • ℓ)) (P S01) A

def signal (r:ℝ) : ℂ:= shear ℓ P r 1 - (16:ℝ) • shear ℓ P r 2
def intervalView (f:ℝ→ℂ) : ℂ:= (16:ℝ) • f 2 - f 1 - ∫ t in (1:ℝ)..(2:ℝ), (4*t^3) • f t

include F
lemma pure_smooth (v:S.Field 4) (hℓ:‖ℓ‖=1) (hr:0<r) : ContinuousOn (YM.FrontierTrace.pure ℓ v r) [[1,2]]:=by
   rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
   intro y hy
   have hh:= smooth_cons S F.room.kernel.smooth (⟨4,v⟩ : S.Tag) (q:=fun _:Fin 1=>⟨4,v⟩)
     (atRoom (aim_ne ℓ hℓ (r*y) (mul_pos hr (zero_lt_one.trans_le hy.1))))
   exact (hh.continuousAt.comp (f:=fun y:ℝ=> (r*y) • ℓ) (show ContinuousAt (fun y:ℝ=> (r*y) • ℓ) y from by fun_prop)).continuousWithinAt
-- bridge actual shear read
lemma stir_reads {a:ℝ} (he:ExactTurns F) (hg:G.Simple) (hF:Paying F P)
     (hℓ:‖ℓ‖=1)(hne:ℓ 0*ℓ 1≠0) (hr:0<r)
     (ha:r^4 • F.sector.energy 0 1 = a • P S01) (t:ℝ)(ht:0<t):
     B F A (r^4) (r*t)=a • shear ℓ P r t := by
   have hv:= slope_angle F A (r^4) (scalarA_ortho F P hF hg he) ℓ hℓ _ (mul_pos hr ht) 0 1
   let x:=atShape ((r*t) • ℓ)
   have heq:(ℓ 0*ℓ 1) • B F A (r^4) (r*t)= a • custom x (P S01) A:= by
      obtain ⟨M,hM⟩ := custom_linear (e:=4) x A
      rw [if_neg (by decide : (0:Axis) ≠1),zero_add] at hv
      rw [← hv]; unfold YM.FrontierTrace.current; rw [ha]; change custom x (a • _) A= _
      rw [hM,hM]; exact (M.restrictScalars ℝ).map_smul ..
   rw [shear, smul_comm a _,← show _ = _ from heq]; exact (inv_smul_smul₀ hne _).symm

theorem integrated_stress {A':S.Field 4}{d:ℝ} {m:ℝ}(hA:∀ g:Ortho,F.sector.turns.act 4 g A'=A')(hr:0<r)
    (hm : m • centered F=(4*d) • A')(h0:expectation S 4 A'=0)(hℓ:‖ℓ‖=1):
    d • intervalView (YM.FrontierTrace.pure ℓ A' r)= (3/4:ℝ) • (B F A' m r - (16:ℝ) • B F A' m (r*2)):=by
   let K := YM.FrontierTrace.pure ℓ A' r
   have hp : IntervalIntegrable (fun t:ℝ=> (4*t^3) • K t) volume 1 2 := ContinuousOn.intervalIntegrable (μ:=volume) (u:=fun t:ℝ=> (4*t^3) • K t) ((show Continuous (fun t:ℝ=>4*t^3) from by fun_prop).continuousOn.smul (pure_smooth F ℓ A' hℓ hr))
   let y := fun t:ℝ=> (4*t^3) • K t
   have heq(t) (ht:0<t) : K t=custom (atShape (slice (r*t))) A' A':= custom_aim F A' hA ℓ hℓ (r*t) (mul_pos hr ht)
   have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t:ℝ=> t^4 • L F A' m (r*t)) (f':=d • y) (a:=1) (b:=2) (fun t ht=>?_) (hp.smul (r:=d))
   rotate_left
   · change HasDerivAt _ (d • ((4*t^3) • K t)) _
     have ht': 0<t:= by rw [uIcc_of_le (by norm_num)] at ht; exact zero_lt_one.trans_le ht.1
     rw [smul_smul,heq _ ht', show d*(4*t^3)=4*d*t^3 by ring]; exact exact_dilation F A' m hA hr t ht' d hm h0
   have hs (t:ℝ)(ht:0<t) : L F A' m (r*t)=d • K t+(3/4:ℝ) • B F A' m (r*t):=by
      rw [heq t ht]; exact sub_eq_iff_eq_add.mp (trace_repaired F A' m hA (mul_pos hr ht) d hm h0)
   have h1 := hs 1 one_pos; have h2:=hs 2 zero_lt_two
   simp only [mul_one] at h1
   simp only [Pi.smul_apply,intervalIntegral.integral_smul,h1,hs 2 zero_lt_two, mul_one,one_pow,one_smul] at he
   change d • ((16:ℝ) • K 2-K 1 - ∫ (t:ℝ) in (1:ℝ)..2, y t)= _
   rw [smul_sub,he]; module

/-- Exact offdiagonal two-radii contrast reading. `a,d` are *actual* weights,
  not perturbative, no determinant in this identity. -/
theorem contrast {a d:ℝ} (he:ExactTurns F) (hg:G.Simple) (hF:Paying F P)
     (hℓ:‖ℓ‖=1)(hne:ℓ 0*ℓ 1≠0) (hr:0<r)
     (ha:r^4 • F.sector.energy 0 1 = a • P S01)
     (hd:r^4 • centered F=(4*d) • scalarA P):
     d • intervalView (KK ℓ P r) = (3/4:ℝ) • a • signal ℓ P r := by
    unfold KK
    rw [integrated_stress F ℓ (scalarA_ortho F P hF hg he) hr hd
          (centers_field F.room.kernel.laws _) hℓ] -- defeq KK? m elaborate
    have ht := stir_reads F ℓ P he hg hF hℓ hne hr ha 1 one_pos
    rw [mul_one] at ht
    rw [ht,stir_reads F ℓ P he hg hF hℓ hne hr ha 2 zero_lt_two]
    unfold signal; module

end YM.FrontierTrace
