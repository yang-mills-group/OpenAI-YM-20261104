import YM.Integration.WilsonMacroscopicRichCaptureSeparation
import YM.Integration.WilsonMacroscopicRichSignedAmplitude

/-! The original continuum running coupling at the actual admitted length, uniformly in every reporting phase. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichContinuumCollar
open Filter Set Lattice Wilson RG OPE Spec RG16 RG16.Literal Pert.Asymptotics Real Trace.Pilot
open PhysicalNext.Repeat.Legato
open private logs from YM.Integration.WilsonMacroscopicRichReportingRate
open scoped Classical Topology
variable {G:Gauge}(R:Run G)

theorem clock (simple:G.Simple)(B:ℝ)(g:ℝ→ℝ)(hg:Coupling G g):∃A:ℝ,0<A ∧ ∀ᶠ m:ℕ in atTop,
    ∀ρ:ℝ,0<ρ→ρ≤(Lambda R.family.path.levels m)^(B+1) →
    0<g (R.family.S.a m*ρ) ∧ R.family.path.levels.clock.hatBeta m*(g (R.family.S.a m*ρ))^2≤A:=by
  let C:=R.family;let A:=C.path.levels;let s:=G.slopeConstant
  have sp:0<s:=Gauge.slopeConstant_pos simple
  let d:=s⁻¹+1
  have dp:0<d:=by unfold d;positivity
  have cp:0<A.clock.bar+s:=add_pos A.clock.bar_pos sp
  obtain ⟨δ,hδ,control⟩:=mem_nhdsGT_iff_exists_Ioo_subset.mp (hg.positive.and (hg.running.eventually (gt_mem_nhds (show s⁻¹<d by dsimp [d];linarith))))
  have grow:=cluster_shrinks C simple 1 B one_pos
  have tilt:=(upper_slow C simple 1 B one_pos).rate.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num))
  refine ⟨2*(A.clock.bar+s)*d,by positivity,?_⟩
  filter_upwards [grow.eventually (gt_mem_nhds hδ),tilt,C.S.divergent.eventually_gt_atTop 1] with m thin width high
  intro ρ positive lo
  have mesh:=C.S.a_pos m
  let r:=C.S.a m*ρ
  have op:0<r:=mul_pos mesh positive
  have small:r<δ:=(show r≤Upper C 1 B m*C.S.a m by simpa [r,Upper,C,mul_comm] using mul_le_mul_of_nonneg_right lo mesh.le).trans_lt thin
  obtain ⟨gp,paid⟩:=control (show r∈Ioo 0 δ from ⟨op,small⟩)
  have ms:0<C.S.scale m:=zero_lt_one.trans high
  have prec:ρ≤Upper C 1 B m:=by simpa [Upper,C] using lo
  have logρ:log ρ≤(C.S.scale m)/2:=by
    have logUpper:log (Upper C 1 B m)<(1/2:ℝ)*C.S.scale m:=(div_lt_iff₀ ms).mp width
    linarith only [log_le_log positive prec,logUpper]
  have effective: C.S.scale m≤2*LogV r:=by
    change log (C.S.a m)⁻¹≤2*log ((C.S.a m)*ρ)⁻¹
    rw [log_inv,log_inv,log_mul mesh.ne' positive.ne']
    change log ρ≤log (C.S.a m)⁻¹/2 at logρ
    rw [log_inv] at logρ;linarith only [logρ]
  have beta: A.clock.hatBeta m≤2*(A.clock.bar+s)*LogV r:=by
    change A.clock.bar+s*C.S.scale m≤_
    have whole:A.clock.bar≤A.clock.bar*C.S.scale m:=by nlinarith only [mul_nonneg A.clock.bar_pos.le (sub_nonneg.mpr high.le)]
    nlinarith only [whole,mul_le_mul_of_nonneg_left effective cp.le]
  refine ⟨gp,?_⟩
  calc _ ≤(2*(A.clock.bar+s)*LogV r)*(g r)^2:=mul_le_mul_of_nonneg_right beta (sq_nonneg _)
       _=2*(A.clock.bar+s)*(LogV r*(g r)^2):=by ring
       _≤_:=mul_le_mul_of_nonneg_left paid.le (by positivity)

theorem original (simple:G.Simple)(pace:∀m,((R.family.S.block m).val:ℝ)≤log (Lambda R.family.path.levels m))
    (M B:ℝ)(hm:0<M)(hb:20<B)(D:ℕ)(g:ℝ→ℝ)(hg:Coupling G g){ε:ℝ}(ep:0<ε):∀ᶠ m:ℕ in atTop,
    let b:=port R.family (8*M) B (mul_pos (by norm_num) hm) m
    ∀ρ:ℝ,(Lambda R.family.path.levels m)^B≤ρ→ρ≤(Lambda R.family.path.levels m)^(B+1) →
    let r:=R.family.S.a m*ρ
    0<g r ∧ R.family.S.a b*(Lambda R.family.path.levels m)^D*g r≤ε*r:=by
  obtain ⟨K,kp,cost⟩:=clock R simple B g hg
  let W:=sqrt K
  have wp:0<W:=sqrt_pos.2 kp
  have ep':0<ε/(8*M*W):=by positivity
  filter_upwards [WilsonMacroscopicRichCaptureSeparation.mesh R simple pace M B hm hb,logs R simple (3+D) ep',cost] with m size logs bill
  intro b ρ below above r
  let L:=Lambda R.family.path.levels m;let β:=R.family.path.levels.clock.hatBeta m
  have lp:0<L:=lambda_pos R.family m
  have bp:0<β:=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have rp:0<ρ:=(rpow_pos_of_pos lp _).trans_le below
  have rr:0<r:=mul_pos (R.family.S.a_pos m) rp
  obtain ⟨gp,paid⟩:=bill ρ rp above
  have sr:0<sqrt β:=sqrt_pos.2 bp
  have wg:sqrt β*g r≤W:=by
    have sq:sqrt β^2=β:=sq_sqrt bp.le
    have w2:W^2=K:=sq_sqrt kp.le
    have eq:(sqrt β*g r)^2=β*(g r)^2:=by rw [mul_pow,sq]
    nlinarith only [eq,w2,paid,mul_nonneg sr.le gp.le,wp]
  have scaled:8*M*(L^(3+D)*g r)≤ε:=by
    calc _ ≤8*M*((ε/(8*M*W)*sqrt β)*g r):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right logs gp.le) (by positivity)
         _=(8*M*(ε/(8*M*W)))*(sqrt β*g r):=by ring
         _≤(8*M*(ε/(8*M*W)))*W:=mul_le_mul_of_nonneg_left wg (by positivity)
         _=ε:=by field_simp [hm.ne',wp.ne']
  refine ⟨gp,?_⟩
  calc _ ≤ ((8*M)*L^3*r)*L^D*g r:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (size ρ below) (pow_nonneg lp.le _)) gp.le
       _=(8*M*(L^(3+D)*g r))*r:=by rw [pow_add];ring
       _≤_:=mul_le_mul_of_nonneg_right scaled rr.le
end YM.Integration.WilsonMacroscopicRichContinuumCollar
