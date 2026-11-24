import YM.Integration.WilsonOriginalPrimerHeardRay

/-! The actual finite copies of the signed shareholder, all retaining
the elected source, its original charge and its independent test. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerReplicatedFields
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n n':Side}{Q d:ℕ}
variable (h:n.val∣n'.val){P:Earn.Passport n Unit}{H:Marker.Census Unit}(S:Earn.Binder P H)

def lifted (u:Fin (Pages n n')):Earn.Binder (FVA1Physical.TwoReset.coverPassport h P u) H where
  mode := S.mode
  front := S.front
  east := S.east
  path a := Cable.link (page h S.center u).val (page h (P.origin a) u).val
  span _ _ := Cable.link_stop ..
  extra := S.extra

theorem site (u:Fin (Pages n n')):(lifted h S u).center=(page h S.center u).val:=rfl

variable (W:Fin (Q+1)→Poetry.Roll G Unit)(C:Fin (Q+1)→ℝ)(σ:ℝ)
variable (paid:∀j,(W j).Faith {()} () (j.val+d+2) (2*σ) (C j))
variable (legal:∀j,(W j).honest)(d0:0<d)
variable (E:Unit→Set ℂ)(cap:∀ t,‖value E t‖≤1)(t:Affinity.Wallet E)(σ0:0<σ)
variable (layout:Layout G)(stock:Finset Age)
local notation "M" => material S W C σ paid legal d0 (value E)
local notation "Y" => copyColor h M (fun _=>d) (fun z=>(M z).paint t) layout stock
local notation "Y₁" u:max => WilsonOriginalPrimerHeardRay.source (lifted h S u) W C σ paid legal d0 E t layout stock

theorem actor (u:Fin (Pages n n'))(z:Name W):
    FVA1Physical.TwoReset.copy h (M z) u=material (lifted h S u) W C σ paid legal d0 (value E) z:=rfl

theorem fields (s:Hot H):
    (Y).mark s=∑u:Fin (Pages n n'),(Y₁ u).mark s:=rfl

theorem degree (s:Hot H)(u:Fin (Pages n n')):
    (Y).power s=(Y₁ u).power s:=rfl

include cap σ0 in
theorem graded (s:Hot H):
    Assembly.GradeAt ((Y).power s) (Bulk.projected ((Y).mark s)):=by
  have wallet:=WilsonOriginalPrimerCourseRead.salary S W C σ paid legal d0 E cap t σ0
  have good (u:Fin (Pages n n')):Assembly.GradeAt ((Y).power s) (Bulk.projected ((Y₁ u).mark s)):=by
    exact Air.grade (fun z=>FVA1Physical.TwoReset.copy h (M z) u) (fun z=>(M z).paint t) (fun _=>d)
      (copy_staff h M (fun _=>d) (fun z=>(M z).paint t) wallet u) layout stock s
  rw [fields]
  unfold Bulk.projected
  simp_rw [Finset.sum_apply]
  exact Assembly.GradeAt.list_sum Finset.univ _ (fun u _=>good u)

include cap σ0 in
theorem discharge (s:Hot H)(j:ℕ)(A:Exterior.fieldDir G n' 1):
    (Air.discharge Y j A).part s.val=
      ∑u:Fin (Pages n n'),(Air.discharge (Y₁ u) j A).part s.val:=by
  have wallet:=WilsonOriginalPrimerCourseRead.salary S W C σ paid legal d0 E cap t σ0
  have smooth (u:Fin (Pages n n')):ContDiffAt ℝ ω (Bulk.projected ((Y₁ u).mark s)) 0:=
    (Air.grade (fun z=>FVA1Physical.TwoReset.copy h (M z) u) (fun z=>(M z).paint t) (fun _=>d)
      (copy_staff h M (fun _=>d) (fun z=>(M z).paint t) wallet u) layout stock s).smooth
  let k:=(Y).power s+j
  have chosen:Bulk.projected ((Y).mark s)=∑u:Fin (Pages n n'),Bulk.projected ((Y₁ u).mark s):=by
    rw [fields];funext y;simp [Bulk.projected]
  simp only [Air.discharge,part_lit,Assembly.jet,chosen]
  rw [iteratedFDeriv_sum_apply (fun u _=>(smooth u).of_le le_top)]
  simp only [_root_.sum_apply,Finset.smul_sum]
  rfl

theorem elsewhere (s:Hot H)(hs:s≠submitted S)(y:ℝ)(U:Config G n'):
    (Y).mark s y U=0:=by
  rw [fields]
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun u _=>WilsonOriginalPrimerHeardRay.elsewhere (lifted h S u) W C σ paid legal d0 E t layout stock s hs y U

end YM.Integration.WilsonOriginalPrimerReplicatedFields
end
