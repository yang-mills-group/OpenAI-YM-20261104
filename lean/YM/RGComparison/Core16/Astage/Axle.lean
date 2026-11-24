import YM.RGComparison.Core16.Astage.Resolve
import YM.RGComparison.Core16.Astage.Persistent
/-!
# Supply rough *filtration pivot* inverse data on the comparison witness

Use a single earlier subrefinement (Beneath F.fuse), not even switching on horizon. Build
U_{m,h} for a candidate comparison using **LOCAL SECTION, root coordinates**, enough for
qru-type bounds. Includes proof of realization via the actual cutoff C.factory on all periods,
not a scheme assumption. No claim these particular primary representatives from the UV-extension
constructor have already been matched to the A formal prescription or analytically reclosed.
Different from the all-address $π^natural$; like the exact denominator, preserve this binding
and prove needed projection or change of frame at the reconstruction step!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Axle
open Filter Function Real Metric Set OPE Columns
open RG Lattice Wilson Push Table Orbits
open Extraction Extra.Histories.Charts Next.UVStress Next.Rank.Price
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
set_option quotPrecheck false
variable {G:Gauge}{C:Family G} {f:Extraction.Order}{S:Table C.book}
   (T:Spec.Final C f S)(H:C.Makes)
local notation "P"=> C.path.levels
local notation "D"=> T.sector.derivatives
variable (d:ℕ)
local notation "F"=> C.labels.level d
local notation "a"=> C.S.a
local notation "L"=> C.path.levels
open Pert.Asymptotics (regulatorRun)
open scoped YM.RGComparison.Core16.Astage.Panel
/-- WINDOW coordinates include the level-threshold costs. Remove the deterministic $a_m^{-d}$
on transfer operands in measuring units and attach g^{-k}$ (not $(Calendar.threshold m)^{-k}$)
on literal curvature slots. Thus a h-weight column reports a **dimensionless actual reading** in
those engineering units. -/
def root (m N p: ℕ) : C.label d →L[ℂ] C.label d:= (Extra.Histories.Charts.window C H d m N p).symm.toContinuousLinearMap.comp
     (LinearMap.toContinuousLinearMap ((↑(C.S.a m^d):ℂ) • (F).scaled (shrink C m N p)⁻¹))
variable {m N p:ℕ}
lemma atCoupling (ht : C.ref d ≤ m)(hN:m≤N)(u:C.label d) :
    let x := root H d m N p u; let T := C.factory d N p
    (F).scaled (L|>.clock.threshold m)⁻¹ (T.entries m (T.terminal.symm x)).x =
       (↑(C.S.a m^d):ℂ) • (C.labels.level d).scaled (regulatorRun C N p m)⁻¹ u:=by
    intro x T; rw [show (T.entries m _).x= _ from (peek C H d N p m ht hN x).symm];
    let W:= Extra.Histories.Charts.window C H d m N p; let g:= regulatorRun C N p m; let t:=(P).clock.threshold m; let S: C.label d:= (F).scaled (shrink C m N p)⁻¹ u
    rw [show W x = (↑(C.S.a m^d):ℂ) • S from W.apply_symm_apply ..,map_smul]
    apply congr_arg; funext i; unfold S; rw [Labels.Frame.scaled_apply,Labels.Frame.scaled_apply,Labels.Frame.scaled_apply, ← mul_assoc, ← Complex.ofReal_mul, ← mul_pow]
    have he:0<t:=(P|>.budget m).threshold_pos; have hg:= shrink_pos C H hN p
    have hQ:t⁻¹ * (shrink C m N p)⁻¹ = g⁻¹:=by rw [show shrink C m N p=g/t from rfl]; field_simp
    rw [show (P).clock.threshold m=t from rfl,hQ]

def cost (C:Family G) (d m:ℕ):ℝ := ∑ i:(C.labels.level d).Index, (2*C.path.levels.clock.monitor m)^(((C.labels.level d).grades i).2)
lemma charge (hi:C.ref d ≤ m)(hp:m≤N)(u:C.label d): quota C d m N p (root H d m N p u) ≤ C.S.a m^d * (cost C d m*‖u‖):=by
    let w:= Extra.Histories.Charts.window C H d m N p; let b:= shrink C m N p; let z:=root H d m N p u; let B:=2*(L).clock.monitor m
    rw [quota, ←peek C H d N p m hi hp _, show w z= (↑(a m^d):ℂ) • (F).scaled b⁻¹ u from w.apply_symm_apply ..]; unfold Labels.Frame.coeffSize cost; simp only [Pi.smul_apply,Labels.Frame.scaled_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos _).le _),norm_mul];
    rw [Finset.sum_mul, Finset.mul_sum];
    have hb:0<b⁻¹:=inv_pos.mpr (shrink_pos C H hp _); have hB:b⁻¹≤ B:=shrink_min C H hp _; apply Finset.sum_le_sum; intro i he
    rw [Real.norm_of_nonneg (pow_nonneg hb.le _)]; refine mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ hb.le hB _) (norm_le_pi_norm u i) (norm_nonneg _) (pow_nonneg (hb.le.trans hB) _)) (pow_nonneg (C.S.a_pos _).le _)

variable (b:Ultrafilter (ℕ×ℕ)) (hp:(b:Filter (ℕ×ℕ))≤ f.fuse)
include H hp

lemma stored (n i:ℕ)(hi:C.ref n ≤ i) : ∃ F':C.label n→L[ℂ]C.label n,
    Tendsto (fun j:ℕ×ℕ=> root H n i j.1 j.2) b (𝓝 F'):=by
    let f (j : ℕ×ℕ):= root H n i j.1 j.2; let U:= b.map f; obtain ⟨D',hD,h⟩:= quota_stop C H hi; let r:= D'*(C.S.a i^n)*(cost C n i)
    have hx:Metric.closedBall (0:C.label n→L[ℂ]C.label n) r∈U:= by
       apply Ultrafilter.mem_map.mpr; change ∀ᶠ j in (b:Filter (ℕ×ℕ)), f j∈Metric.closedBall 0 r
       have hV:0 ≤ cost C n i:= Finset.sum_nonneg (fun _ _=> pow_nonneg (mul_nonneg zero_le_two (exp_nonneg _)) _)
       filter_upwards [((Cards.largeMesh _).eventually_ge_atTop i).filter_mono hp] with j hj
       apply mem_closedBall_zero_iff.mpr; apply (f j).opNorm_le_bound (show 0 ≤ r from by unfold r; have hh:= C.S.a_pos i; positivity); intro z
       simp_rw [r,mul_assoc]; exact (h _ _ _ hj).trans (mul_le_mul_of_nonneg_left (charge H n hi hj z) hD)
    obtain ⟨F',hF,ht⟩:= isCompact_closedBall _ _|>.ultrafilter_le_nhds' _ hx; exact ⟨F',ht⟩
variable {R:Reader (T.sector.derivatives) T.sector.turns T.room.kernel.spin}

structure TransferLimit (C:Family G) (H:C.Makes) (b:Filter (ℕ×ℕ)) where
    fieldMap (d m:ℕ): C.label d→L[ℂ] C.label d
    lim (d m:ℕ)(h:C.ref d ≤ m): Tendsto (fun j:ℕ×ℕ=> root H d m j.1 j.2) b (𝓝 (fieldMap d m))

lemma option : Nonempty (TransferLimit C H b):=by
    choose! P1 hP using stored (f:=f) H b hp; exact ⟨⟨P1,hP⟩⟩

omit H hp
variable {l:Filter (ℕ×ℕ)} [l.NeBot] (hl:l≤f.fuse) (U:TransferLimit C T.room.cutoff l)
def full (i:ℕ): C.label d→L[ℂ] S.Field d := (LinearMap.toContinuousLinearMap (S.project d)).comp (U.fieldMap d i)
structure Crew (l:Filter (ℕ×ℕ)) {ι:Type}{κ:Filter ι}{m:ι→ℕ}{d:ℕ} (v:ι→ S.Field d): Prop where
    receipts : ∃ p:ι→ℝ, RateLE κ (ruler C m) p (-(d:ℝ)) ∧
        ∀ᶠ i in κ, ∃ (x:C.label d)(u:ℕ×ℕ→ C.label d), Tendsto u l (𝓝 x) ∧
          S.project d x=v i ∧ ∀ᶠ j in l, quota C d (m i) j.1 j.2 (u j) ≤ p i

variable {ι:Type}{κ:Filter ι} [κ.NeBot]{m':ι→ℕ}
   (r: Reader (T.sector.derivatives) T.sector.turns T.room.kernel.spin)
   (B:Services C f S) (ht:Tendsto m' κ atTop)
include ht
local notation "s"=> ruler C m'
omit [κ.NeBot] in
lemma ruler_height : Height C.S κ s m' 1:= ⟨ht, tendsto_const_nhds.congr' (by
    filter_upwards [(large_s C ht).eventually_gt_atTop 0] with i hi; rw [show C.S.scale (m' i)= ruler C m' i from rfl,div_self hi.ne'])⟩
include B
omit [κ.NeBot] in
lemma coupling_cost : RateLE κ (budgetLog C m') (fun i=> cost C d (m' i)) 0:= RateLE.sum (large_Λ C B.simpleGate ht) (fun j _=> by apply RateLE.mono ((RateLE.const (2:ℝ) (large_Λ C B.simpleGate ht)|>.mul (slow_stage B.simpleGate ht m' ht (by simp))).pow _ (large_Λ C B.simpleGate ht)); simp)
-- ^ for hull spatial price; don't apply directly to log/C reader output.
omit [κ.NeBot] in
lemma homogeneous : RateLE κ s (fun i=> a (m' i)^d * cost C d (m' i)) (-(d:ℝ)):=by
    apply RateLE.mono ((RateLE.pow d ((ruler_height (C:=C) ht).mesh.pays (large_s C ht)) (large_s C ht)).mul (hb (b:=B)))
    simp
where hb (b:Services C f S) : RateLE κ s (fun i=> cost C d (m' i)) 0:=by
       intro v hv
       have hH:= coupling_cost (C:=C) d b ht 1 (by norm_num)
       filter_upwards [hH,(negligible C b.simpleGate ht).eventually (ge_mem_nhds hv),(large_s C ht).eventually_gt_atTop 0] with i hi hv hZ; exact hi.trans (Real.exp_monotone ((one_mul _).trans_le ((div_le_iff₀ hZ).mp hv)))
include hl
omit [κ.NeBot] [l.NeBot] in
lemma on_roots (v:ι→ C.label d)(hv:RateLE κ s v 0): Crew l (κ:=κ) (m:=m') (fun i=>full T d U (m' i) (v i)):=by
    refine ⟨fun i=> (a (m' i))^d * cost C d (m' i)*‖v i‖,((homogeneous (C:=C) d B ht).mul hv.norm|>.mono (by rw [add_zero])),?_⟩
    filter_upwards [ht.eventually_ge_atTop (C.ref d)] with i hk
    let h:= T.room.cutoff; let k:= m' i; let y:= v i; refine ⟨U.fieldMap d k y,fun j=> root h d k j.1 j.2 y,?_, rfl,?_⟩
    · exact ((ContinuousLinearMap.apply ℂ (C.label d) y).continuous.continuousAt.tendsto).comp (U.lim d k hk)
    filter_upwards [((Cards.largeMesh f).eventually_ge_atTop k).filter_mono hl] with i hi; rw [mul_assoc]; exact charge h d hk hi y

omit [κ.NeBot] in
lemma crew_budget (v:ι→ S.Field d)(hc:Crew l (κ:=κ) (m:=m') v) (j:ℕ)(hj:j≤d) : RateLE κ s (fun i=> r.cutTest j d (v i)) (-(j:ℝ)):=by
    obtain ⟨W,g,D',he⟩:= B.purchase; obtain ⟨A,V,E,Q,b⟩:= B.along; obtain ⟨p,hp,hv⟩:= hc.receipts
    let L':= r.cutTest j d; let P':= L'.comp (S.project d); let P0:= LinearMap.toContinuousLinearMap P'; have hh:= RateLE.const ‖P0‖ (large_s C ht)
    have hk:= ruler_height (C:=C) ht
    cases j with
    | zero=>
       let z i:= juice C.path.levels (m' i) * (C.S.a (C.ref d)/a (m' i))^d
       have hpos i:0 ≤ z i:=mul_nonneg (zero_le_one.trans (juice_pos ..)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)
       have hQ: RateLE κ (ruler C m') z (d:ℝ):=by
           have hQ:=((juice_rate_seq C ht hk.pace).mul (((RateIs.const (large_s C ht) (C.S.a_pos (C.ref d))).div hk.mesh).power d)).pays (large_s C ht)
           exact hQ.mono (by simp)
       apply ((hh.mul (hQ.mul hp)).mono (by simp)).of_norm_le
       filter_upwards [hv, ht.eventually_ge_atTop (C.ref d)] with i ⟨x,y,hY,hX,hz⟩ hi
       have hx: ‖x‖ ≤ z i * p i:= by
            apply le_of_tendsto hY.norm; filter_upwards [((Cards.largeMesh f).eventually_ge_atTop (m' i)).filter_mono hl, hz] with j hj hz; exact (whole_origin (p:=j.2) b _ hi (show m' i ≤ j.1 from hj)).trans (mul_le_mul_of_nonneg_left hz (hpos i))
       rw [← hX]
       exact (P0.le_opNorm x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg P0))
    | succ j=>
       have hQ:= fare_rate (d:=d) (e:=j) he.toTableTickets ht (large_s C ht) hk.pace|>.pays (large_s C ht)
       apply ((hh.mul (hQ.mul hp)).mono (by push_cast [Nat.cast_sub hj]; linarith)).of_norm_le
       filter_upwards [hv,ht.eventually_ge_atTop (C.ref d)] with i ⟨x,y,hY,hX,hz⟩ hi
       obtain ⟨w,⟨u,hw⟩,hf⟩:= limit_cap he.toTableTickets B.simpleGate b r.lifts (show j<d from hj) y x hl hi hz hY -- p binder?
       have h:P0 w=0:=by change (L' (S.project d w))=0; rw [← hw]; unfold L'; rw [r.cut_rise, r.kills_lower _ _ (Nat.lt_succ_self j)]
       rw [← hX]; change ‖P0 x‖ ≤ _; rw [← sub_zero (P0 x),← h,← map_sub]
       exact (P0.le_opNorm (x-w)).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg P0))
end YM.RGComparison.Core16.Astage.Axle
