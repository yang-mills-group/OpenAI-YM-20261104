import YM.Integration.WilsonSeparatedOwnLength
import YM.Integration.WilsonMacroscopicRichRegister

/-! The two-point rich probe translated to its own origin has genuine
clearance on its *entire prescribed support* at a moving reporter length.
The true plotted near grid is disjoint from this translated probe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMovingRichGeometry
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Filter Set MeasureTheory Lattice Extraction Table Spec Climb OPE OPE.Orbits RG17 SharpGram PhysMS
open Trace.Pilot Frontier6.Road SharedIntrinsicWilsonGrid
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {I:Type} [Fintype I] {d:I→ℕ} {D:ℕ}

def far (τ:ℝ) (z:Points 2) : Fin 1→E4 := fun i=>τ • (z i.succ-z 0)

private theorem distinct {C:Family G} {b m j:ℕ} {x:I → Cover} (plot:Plot C b m j x)
    {E:Type} [Fintype E] {y:E→E4} {η:ℝ} (ηp:0<η) (width:C.S.a (m+1)<η) (clear:ClearOf 0 y η) :
    Injective (beside (C.S.gridPoint j ∘ x) y) := by
  let near:=C.S.gridPoint j ∘ x
  have inner : Injective near := by
    intro k l eq
    by_contra ne
    have h:=plot.spaced k l ne
    change 2*C.S.a j*((C.path.levels.budget j).B:ℝ)^2<‖near k-near l‖ at h
    rw [eq,sub_self,norm_zero] at h
    exact (not_lt_of_ge (mul_nonneg (mul_nonneg (by norm_num) (C.S.a_pos _).le) (sq_nonneg _))) h
  have outer : Injective y := by
    intro k l eq
    by_contra ne
    have h:=clear.spread k l ne
    rw [eq,sub_self,norm_zero] at h
    exact ηp.not_ge h
  apply beside_distinct.mpr
  refine ⟨inner,outer,?_⟩
  intro k l eq
  have h:=clear.openSpace l
  change η≤‖(0:E4)-y l‖ at h
  change near k=y l at eq
  rw [zero_sub,norm_neg,←eq] at h
  have fit:=plot.fit k
  change 8*‖near k‖<C.S.a (m+1) at fit
  linarith only [fit,width,h,norm_nonneg (near k)]

theorem original (φ:Test 2) (P:Plan C D (Fintype.card I) (∑ i,d i)) {a b:ℝ}
    (ap:0<a) (ab:a<b) (edge:3*b<P.h) :
    ∀ᶠ r in trail,∀ z∈tsupport φ,ClearOf 0 (far (r^a) z) (r^b) ∧
    ∀ x:I → Cover,Plot C (P.b r) (P.middle r) (P.j r) x→Injective (beside (C.S.gridPoint (P.j r) ∘ x) (far (r^a) z)) := by
  obtain ⟨M,δ,hM,dp,supported⟩:=RG17.roomCosts (K:=tsupport φ) φ.hasCompactSupport φ.tsupport_subset
  have lim:=PhysMS.to_log_zoom
  have width:∀ᶠ r in trail,C.S.a (P.middle r)<r^b := by
    have h:=(PhysMS.length_rate.rpow b).overtakes (P.mid.mesh.pays lim) lim (by
      simp only [mul_neg,mul_one]; linarith only [P.before,edge,ap,ab])
    simpa only [id_eq] using h
  have clearance:∀ᶠ r in trail,r^b<δ*r^a := by
    have h:=((RateIs.const lim dp).mul (PhysMS.length_rate.rpow a)).overtakes
      ((PhysMS.length_rate.rpow b).pays lim) lim (by simp only [zero_add,mul_neg,mul_one];linarith only [ab])
    simpa only [id_eq] using h
  filter_upwards [width,clearance,PhysMS.length_rate.pos] with r thin room rp z hz
  have openAt : ClearOf 0 (far (r^a) z) (r^b) := by
    constructor
    · intro i
      have hs := (supported 1 one_pos z hz).spaced i.succ 0 (Fin.succ_ne_zero i)
      have mesh : δ≤‖z i.succ-z 0‖ := by simpa [RG17.posed] using hs
      have far0:0≤r^a := Real.rpow_nonneg rp.le _
      change r^b≤‖(0:E4)-r^a • (z i.succ-z 0)‖
      rw [zero_sub,norm_neg,norm_smul_of_nonneg far0]
      exact room.le.trans ((mul_comm δ (r^a)).le.trans (mul_le_mul_of_nonneg_left mesh far0))
    · intro i j h;exact (h (Subsingleton.elim _ _)).elim
  refine ⟨openAt,fun x hx=>distinct hx (Real.rpow_pos_of_pos rp _) ?_ openAt⟩
  exact (C.S.strictAnti (Nat.lt_succ_self _)).trans thin

end YM.Integration.WilsonSeparatedMovingRichGeometry
