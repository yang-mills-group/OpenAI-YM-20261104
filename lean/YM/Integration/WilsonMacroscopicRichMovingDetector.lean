import YM.Integration.WilsonMacroscopicRichContinuumCollar
import YM.Integration.WilsonMacroscopicRichSubscribedTest

/-! The signed physical detector beyond the full original capture, including lifted subcell placements. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichMovingDetector
open Filter Function Set Lattice Wilson RG OPE Spec RG16 RG16.Literal Pert.Asymptotics Real Trace.Pilot Climb PhysMS RG17
open PhysicalNext.Repeat.Legato WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichSignedAmplitude
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f:Extraction.Order}{n:ℕ}

private theorem lengths (simple:G.Simple)(B:ℝ){P:ℝ→Prop}(event:∀ᶠ r in trail,P r):∀ᶠ m:ℕ in atTop,
    ∀ρ:ℝ,0<ρ→ρ≤(Lambda R.family.path.levels m)^(B+1) → P (R.family.S.a m*ρ):=by
  obtain ⟨δ,dp,control⟩:=mem_nhdsGT_iff_exists_Ioo_subset.mp event
  filter_upwards [(cluster_shrinks R.family simple 1 B one_pos).eventually (gt_mem_nhds dp)] with m thin ρ rp hi
  apply control
  refine ⟨mul_pos (R.family.S.a_pos m) rp,?_⟩
  exact (show R.family.S.a m*ρ≤Upper R.family 1 B m*R.family.S.a m by simpa [Upper,mul_comm] using mul_le_mul_of_nonneg_right hi (R.family.S.a_pos m).le).trans_lt thin

/-- All support positions of the genuine dilated independent detector remain away from every real point
in the enlarged physical collar. The signed test is bounded on this very same two-length placement. -/
theorem original (F:Spec.Final R.family f S)(J:ℝ→tower S)(lead:Leading F J)(simple:G.Simple)
    (pace:∀m,((R.family.S.block m).val:ℝ)≤log (Lambda R.family.path.levels m))(M B:ℝ)(hm:0<M)(hb:20<B)(D k:ℕ)(kp:0<k)
    (g:ℝ→ℝ)(hg:Coupling G g)(d:Caps (n+1))(φ:Test 2)(K:Set (Points n))(compact:IsCompact K)(safe:K⊆conf n):
    ∃δ:ℝ,0<δ ∧ ∃C:ℝ,0≤C ∧ ∀ᶠ m:ℕ in atTop,
    let b:=port R.family (8*M) B (mul_pos (by norm_num) hm) m
    ∀ρ:ℝ,(Lambda R.family.path.levels m)^B≤ρ→ρ≤(Lambda R.family.path.levels m)^(B+1) →
    let r:=R.family.S.a m*ρ
    let τ:=r/(g r)^k
    ∃tp:0<τ,
      (∀z∈tsupport φ,∀y t:E4,‖y‖≤M*r→dist t y≤R.family.S.a b*(Lambda R.family.path.levels m)^D→
        δ*τ≤dist t (τ•(z 1-z 0))) ∧
      ∀x∈K,∀u:∀i,(Bel R.family.book).Field (d i),
        let tags:Fin (n+1)→(Bel R.family.book).Tag:=fun i=>⟨d i,u i⟩
        ‖reading J φ tp (tags (Fin.natAdd n 0)) r x (fun i=>tags (Fin.castAdd 1 i))‖≤
           (∫z:Points 2,‖φ z‖)*C*∏i,‖u i‖:=by
  obtain ⟨_,δ,_,dp,room⟩:=RG17.roomCosts φ.hasCompactSupport φ.tsupport_subset
  have far(z:Points 2)(hz:z∈tsupport φ):δ≤‖z 1-z 0‖:=by simpa [posed] using (room 1 one_pos z hz).spaced (1:Fin 2) 0 (by decide)
  obtain ⟨η,ep,C,cp,U,hu,paid⟩:=WilsonMacroscopicRichSubscribedTest.original F J lead d φ K compact safe
  let τ(r:ℝ):=r/(g r)^k
  have rate:=length_rate.div ((coupling_rate hg simple).power k)
  have tr:Tendsto τ trail trail:=tendsto_nhdsWithin_iff.mpr ⟨rate.tends (by simp only [mul_zero,sub_zero];norm_num) to_log_zoom,rate.pos⟩
  have g0:=Trace.Pilot.Coupling.conforms simple hg
  have small:∀ᶠ r in trail,r∈U ∧ τ r∈U ∧ 0<g r ∧ g r<1 ∧ g r< min η (δ/(4*M)):=by
    have inU:∀ᶠ r in trail,r∈U:=hu
    exact inU.and ((tr.eventually inU).and (hg.positive.and ((g0.eventually (gt_mem_nhds zero_lt_one)).and (g0.eventually (gt_mem_nhds (lt_min ep (by positivity)))))))
  have gate:=lengths R simple B small
  have aperture:=WilsonMacroscopicRichContinuumCollar.original R simple pace M B hm hb D g hg (div_pos dp (by norm_num:(0:ℝ)<4))
  refine ⟨δ/2,half_pos dp,C,cp,?_⟩
  filter_upwards [aperture,gate] with m collar admit
  intro b ρ lo hi r t
  have lp:=lambda_pos R.family m
  have rp:0<ρ:=(rpow_pos_of_pos lp _).trans_le lo
  have pp:0<r:=mul_pos (R.family.S.a_pos m) rp
  obtain ⟨in_r,in_t,gp,below,smallg⟩:=admit ρ rp hi
  have power:0<(g r)^k:=pow_pos gp k
  have unit:(g r)^k≤g r:=by simpa only [pow_one] using pow_le_pow_of_le_one gp.le below.le (show 1≤k from kp)
  have tp:0<t:=div_pos pp power
  have length:t*(g r)^k=r:=div_mul_cancel₀ r power.ne'
  have coeff:r/t=(g r)^k:=(div_eq_iff tp.ne').mpr (by simpa only [mul_comm] using length.symm)
  have near:M*r ≤ δ/4*t:=by
    have thin:g r<δ/(4*M):=smallg.trans_le (min_le_right _ _)
    have p:(g r)^k*(4*M)<δ:=(lt_div_iff₀ (by positivity)).mp (unit.trans_lt thin)
    rw [←length];nlinarith only [mul_le_mul_of_nonneg_right p.le tp.le]
  have live:R.family.S.a b*(Lambda R.family.path.levels m)^D ≤ δ/4*t:=by
    have h: (R.family.S.a b*(Lambda R.family.path.levels m)^D)*(g r)^k ≤δ/4*r:=
      (mul_le_mul_of_nonneg_left unit (mul_nonneg (R.family.S.a_pos b).le (pow_nonneg lp.le _))).trans (collar ρ lo hi).2
    have h' : (R.family.S.a b*(Lambda R.family.path.levels m)^D)*(g r)^k ≤ (δ/4*t)*(g r)^k :=h.trans_eq (by rw [mul_assoc,length])
    exact le_of_mul_le_mul_right h' power
  refine ⟨tp,?_,paid r in_r t in_t tp (coeff ▸ (unit.trans (smallg.le.trans (min_le_left _ _))))⟩
  intro z hz y u size distance
  have near_t:‖u‖≤δ/4*t+δ/4*t:=by
    calc ‖u‖=dist u 0:=(dist_zero_right _).symm
         _≤dist u y+dist y 0:=dist_triangle _ _ _
         _≤_:=add_le_add (distance.trans live) (by rw [dist_zero_right];exact size.trans near)
  have away:t*δ≤‖t•(z 1-z 0)‖:=by rw [norm_smul_of_nonneg tp.le];exact mul_le_mul_of_nonneg_left (far z hz) tp.le
  have triangle:‖t•(z 1-z 0)‖≤dist u (t•(z 1-z 0))+‖u‖:=by
    calc ‖t•(z 1-z 0)‖=dist (t•(z 1-z 0)) 0:=(dist_zero_right _).symm
         _≤dist (t•(z 1-z 0)) u+dist u 0:=dist_triangle _ _ _
         _=dist u (t•(z 1-z 0))+‖u‖:=by rw [dist_comm _ u,dist_zero_right]
  linarith only [near_t,away,triangle]
end YM.Integration.WilsonMacroscopicRichMovingDetector
