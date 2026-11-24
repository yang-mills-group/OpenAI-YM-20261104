import YM.Integration.WilsonCapturedPrimaryPointFiniteMatrix

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPointInverse
open Function Filter Finset Lattice Laurent Wilson RG Precision FormalBulk08
open Next.Free Flat Stationary Kemp Pose Gorge Reef Mesa Exterior
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations RG16 RG16.Literal RG16.Guarding
open Pert.Asymptotics Trace.Physical
open WilsonCapturedPrimaryPointBasis WilsonCapturedPrimaryPointRectangle WilsonPointChildFiledPress
open scoped Classical Topology BigOperators
variable {G:Gauge}{d D:ℕ}

def combine (F:Frame G d)(b:F.Index→F.Coeff):F.Coeff→ₗ[ℂ]F.Coeff where
  toFun x row:=∑j,x j*b j row
  map_add' x y:=by ext row;simp [add_mul,Finset.sum_add_distrib]
  map_smul' c x:=by ext row;simp [Finset.mul_sum,mul_assoc]

theorem sale (F:Frame G d)(b:F.Index→F.Coeff){δ:ℝ}
    (close:∀i j,‖b j i-(if i=j then (1:ℂ) else 0)‖≤δ)
    (tight:(Fintype.card F.Index:ℝ)*δ≤1/2):
    ∃S:F.Coeff≃ₗ[ℂ]F.Coeff,(∀x,S x=combine F b x) ∧
      ∀y,F.coeffSize (S.symm y)≤2*F.coeffSize y:=by
  classical
  let A:=combine F b
  have residue (x:F.Coeff)(i:F.Index):
      A x i-x i=∑j,x j*(b j i-(if i=j then (1:ℂ) else 0)):=by
    simp [A,combine,mul_sub,Finset.sum_sub_distrib,mul_ite]
  have per (x:F.Coeff)(i:F.Index):‖A x i-x i‖≤δ*F.coeffSize x:=by
    rw [residue]
    calc
      _ ≤ ∑j,‖x j*(b j i-(if i=j then (1:ℂ) else 0))‖:=norm_sum_le _ _
      _ ≤ ∑j,δ*‖x j‖:=Finset.sum_le_sum fun j _=>by
        rw [norm_mul,mul_comm δ];exact mul_le_mul_of_nonneg_left (close i j) (norm_nonneg _)
      _ = _:=by simp only [Frame.coeffSize,Finset.mul_sum]
  have bound(x:F.Coeff):F.coeffSize x≤2*F.coeffSize (A x):=by
    have localPrice(i:F.Index):‖x i‖≤‖A x i‖+δ*F.coeffSize x:=by
      calc
        _ = ‖A x i-(A x i-x i)‖:=by rw [sub_sub_cancel]
        _ ≤ ‖A x i‖+‖A x i-x i‖:=norm_sub_le _ _
        _ ≤ _:=add_le_add_right (per x i) _
    have sum:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>localPrice i
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at sum
    change F.coeffSize x≤F.coeffSize (A x)+(Fintype.card F.Index:ℝ)*(δ*F.coeffSize x) at sum
    have nonneg:0≤F.coeffSize x:=Finset.sum_nonneg fun i _=>norm_nonneg _
    have small:=mul_le_mul_of_nonneg_right tight nonneg
    linarith only [sum,small]
  have inj:Function.Injective A:=by
    intro x y h
    have z:A (x-y)=0:=by rw [map_sub,h,sub_self]
    have atZero:=bound (x-y)
    rw [z,show F.coeffSize 0=0 by simp [Frame.coeffSize],mul_zero] at atZero
    apply sub_eq_zero.mp;ext i
    have piece:‖(x-y) i‖≤F.coeffSize (x-y):=
      Finset.single_le_sum (fun j _=>norm_nonneg ((x-y) j)) (Finset.mem_univ i)
    exact norm_le_zero_iff.mp (piece.trans atZero)
  let S:=LinearEquiv.ofBijective A ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩
  refine ⟨S,fun _=>rfl,fun y=>?_⟩
  have actual := bound (S.symm y)
  rwa [show A (S.symm y)=y from S.apply_symm_apply y] at actual

theorem tiny (R:Run G)(simple:G.Simple){b:ℝ}(positive:0<b):
    ∀ᶠi:ℕ in atTop,∀N per:ℕ,i≤N→0<regulatorRun R.family N per i ∧ regulatorRun R.family N per i≤b:=by
  filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (2*(b⁻¹)^2)]
    with i warm
  intro N per live
  let β:=R.family.path.β N per i
  have band:=(R.makes.wilson.represents N per i live).band.1
  change R.family.path.levels.clock.hatBeta i/2≤β at band
  have floor:(b⁻¹)^2≤β:=by linarith only [warm,band]
  have bp:0<β:=(sq_pos_of_pos (inv_pos.mpr positive)).trans_le floor
  have good:=Real.sqrt_le_sqrt floor
  rw [Real.sqrt_sq (inv_nonneg.mpr positive.le)] at good
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr bp),?_⟩
  change (Real.sqrt β)⁻¹≤b
  exact (inv_le_comm₀ (Real.sqrt_pos.mpr bp) positive).mpr good

end YM.Integration.WilsonCapturedPrimaryPointInverse
