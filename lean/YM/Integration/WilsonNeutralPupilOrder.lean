import YM.Integration.WilsonNeutralReportedLinkChart
import YM.Integration.WilsonOriginalFiledCopiedStep

/-! The real tested direction at the located parent and independence of
the marked pupil read from the silent layout slot on this held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPupilOrder
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Push.Uniform AllOrder AllOrder.Floe AllOrder.Floe.Step Comparison QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Sunrise Comparison.RG02.Bulk
open Comparison.RG02 Comparison.RG02.Assembly Marker Multi
open FVA1Physical.TwoReset PertExtension.Series Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Classical BigOperators ContDiff


open Comparison.RG02.Moving Comparison.RG02.Moving.Shift Comparison.RG02.Moving.Path Comparison.RG02.Adjacent
open Comparison.RG02.Order Comparison.RG02.Assembly Tensor
local notation "degree" => (ω:WithTop ℕ∞)

theorem triangular {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:Adjacent.Display E)
    (K:UnitCost){e k r:ℕ}(read:e≤k)(paid:k≤r)(z:E)
    (known:∀j≤r,ContDiff ℝ degree (U j)):
    Adjacent.born U K 0 r e z=Adjacent.born U K 0 k e z:=by
  let a (j:ℕ)(t:ℝ):=(K.rating t:ℂ)^j*U j ((K.rating t)⁻¹ • z)
  have hc (j:ℕ)(hj:j≤r):ContDiffAt ℝ degree (a j) 0:=
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp 0 K.smooth).pow j).mul
      ((known j hj).contDiffAt.comp 0 ((K.smooth.inv (by rw [K.origin];norm_num)).smul contDiffAt_const))
  let f (j:ℕ)(t:ℝ):=(t:ℂ)^j*a j t
  have hq (j:ℕ)(hj:j≤r):ContDiffAt ℝ degree (f j) 0:=
    (Complex.ofRealCLM.contDiff.contDiffAt.pow j).mul (hc j hj)
  have price (p:ℕ)(hp:p≤r):Adjacent.born U K 0 p e z=∑j∈range (p+1),motion (f j) e:=by
    have hg (t:ℝ):ages U 0 p t (K.rating t) z=∑j∈range (p+1),f j t:=by
      simp only [ages,zpow_zero,Complex.ofReal_one,one_mul,cover]
      apply Finset.sum_congr rfl
      intro j _
      simp only [f,a,mul_pow,Complex.ofReal_mul,mul_assoc]
    unfold Adjacent.born
    simp_rw [hg]
    exact msum _ _ fun j hj=>hq j (le_trans (mem_range_succ_iff.mp hj) hp)
  rw [price r le_rfl,price k paid]
  symm
  apply sum_subset (range_mono (Nat.succ_le_succ paid))
  intro j hj outside
  have big:¬j≤e:=by have h:=mem_range_succ_iff.not.mp outside;omega
  exact (mono_price (k:=j) (n:=e) (hc j (mem_range_succ_iff.mp hj))).trans (if_neg big)

theorem smooth {G:Gauge}{V ι X:Type}[DecidableEq V][Fintype V]{c n:Side}
    {J:Earn.Passport n V}{R:Census V}(h:n.val∣c.val)(M:ι→Row J R G X)(w:V→ℕ)(L:Layout G)(T:Finset Age)
    (x:X)(j:ℕ)(s:Multi.Hot R):
    ContDiff ℝ degree (fun B:Stationary.Link G c=>(peek h M w L T x j B).part s.val):=by
  let Q:=copyColor h M w (fun i=>(M i).paint x) L T
  let v:=Q.power s+j
  let A:=iteratedFDeriv ℝ v (Bulk.projected (Q.mark s)) 0
  have diag:ContDiff ℝ degree (fun y=>(v.factorial:ℝ)⁻¹ • Tensor.diagonal A y):=
    (Tensor.diag_smooth A degree).const_smul ((v.factorial:ℝ)⁻¹)
  have path:ContDiff ℝ degree (fun y:Stationary.Link G c=>((1:ℝ),Stationary.arm G c 1 y)):=
    contDiff_const.prodMk (Stationary.arm G c 1).contDiff
  unfold peek Air.discharge
  simp only [part_lit]
  exact diag.comp path

end YM.Integration.WilsonNeutralPupilOrder
end
