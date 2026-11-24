import YM.Integration.WilsonOriginalCompoundVertex

/-! Choose the marked compound's strip below its actual covered vacuum sleeve before block length. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompoundVertexStrip
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonOriginalCompoundStrip
open scoped Classical BigOperators
universe u
variable {G:Gauge}

private def part (G:Gauge)(K:KernelChoices)(t j:ℕ):ℝ:=
  if valid:4 ≤ t ∧ 5 ≤ j then splash G K t j valid.1 valid.2 / 2 else 1

private theorem part_pos (G:Gauge)(K:KernelChoices)(t j:ℕ):0<part G K t j:=by
  unfold part
  split
  · rename_i h;exact half_pos (spatter G K t j h.1 h.2).1
  · exact one_pos

/-- The two true stage successors are known before the block. -/
def reserve (G:Gauge)(K:KernelChoices)(j:ℕ):ℝ:=min (part G K j j) (part G K j (j+1))

theorem room (G:Gauge)(K:KernelChoices)(j:ℕ):0<reserve G K j:=
  lt_min (part_pos ..) (part_pos ..)

def narrowed (Q:Request G):Request G where
  radius K j H:=min (Q.radius K j H) (reserve G K j*(16*Q.multiplier H))
  positive K j H:=lt_min (Q.positive K j H) (mul_pos (room G K j) (mul_pos (by norm_num) (Q.grows H)))
  multiplier:=Q.multiplier
  grows:=Q.grows
  entrance:=Q.entrance

theorem widths (Q:Request G)(K:KernelChoices)(j H:ℕ):
    width (narrowed Q) K j H ≤ width Q K j H ∧ width (narrowed Q) K j H ≤ reserve G K j:=by
  have positive:0<16*Q.multiplier H:=mul_pos (by norm_num) (Q.grows H)
  constructor
  · apply min_le_min_left
    exact div_le_div_of_nonneg_right (min_le_left ..) positive.le
  · apply (min_le_right ..).trans
    apply (div_le_iff₀ positive).2
    exact min_le_right ..

theorem actual (R:Run G)(m:ℕ)(ready:5 ≤ R.family.path.levels.clock.J (m+1)):
    reserve G R.metals.p.kernel (R.family.path.levels.clock.J m) ≤ crestM R.family.path.levels m ready/2:=by
  let A:=R.family.path.levels
  let t:=A.clock.J m
  have ht:4 ≤ t:=A.clock.adm m
  have source:part G R.metals.p.kernel t (A.clock.J (m+1))=crestM A m ready/2:=by
    rw [part,dif_pos ⟨ht,ready⟩]
    unfold crestM
    have kernel:A.clock.kernel=R.metals.p.kernel:=R.alloy.B.valid.kernel
    rw [kernel]
  have near:A.clock.J (m+1)=t ∨ A.clock.J (m+1)=t+1:=by
    have low:A.clock.J m ≤ A.clock.J (m+1):=A.fits.mono (Nat.le_succ m)
    have high:A.clock.J (m+1) ≤ A.clock.J m+1:=A.fits.stepSlow m
    dsimp only [t]
    omega
  change reserve G R.metals.p.kernel t ≤ crestM A m ready/2
  rw [←source]
  rcases near with left|right
  · rw [left];exact min_le_left ..
  · rw [right];exact min_le_right ..

theorem original (Q:Request G)(R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (paid:FundedMarkedCoverRows.prices v R.kit)(e:ℕ):
    ∀ᶠ first:ℕ in atTop,∃V:Realm G (e+1) Credit.leanC,V.draws=R.family.path.levels ∧ V.paid=R.metals.O ∧
      V.y=zz R.family.path.levels ∧ V.anchor=first ∧ ∀m (hm:V.anchor ≤ m),
      let A:=R.family.path.levels
      let s:=(V.mint m hm).σ
      ∃ready:5 ≤ A.clock.J (m+1),s=crestM A m ready ∧
      (∀H:ℕ,width (narrowed Q) R.metals.p.kernel (A.clock.J m) H ≤ s/2) ∧
      ∀a (ha:a ≤ e+1) k r,WilsonOriginalCompoundVertex.Income R m a k r s
        ((WilsonOriginalCompoundVertex.tariff G e a k r ha).buy (Borough.ageZ (A.clock.hatBeta m))):=by
  filter_upwards [FundedMarkedCoverRows.realm R simple v paid 0 (fun _=>0) (fun _=>1)
    (fun _=>by decide) e 0 0] with first hfirst
  obtain ⟨V,levels,chart,clock,ancestor,_,_,_,menu⟩:=hfirst
  refine ⟨V,levels,chart,clock,ancestor,?_⟩
  intro m hm A s
  obtain ⟨ready,stamp,_⟩:=menu m (ancestor ▸ hm) hm
  refine ⟨ready,stamp,fun H=>?_,?_⟩
  · change _ ≤ (V.mint m hm).σ/2
    rw [stamp]
    exact (widths Q R.metals.p.kernel (A.clock.J m) H).2.trans (actual R m ready)
  intro a ha k r N M date lifted θ
  have reading:=((Fk.export_domain G Credit.leanC (e+1) a k r ha).choose_spec.money V m hm).2 N M date lifted
  obtain ⟨action,limit,trunk,shelf⟩:=reading
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [s,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using action
  · simpa only [s,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using limit
  · simpa only [s,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using trunk
  intro live
  have cell:=shelf live
  simpa only [s,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using And.intro cell.1 cell.2.1

theorem funded (Q:Request G)(cap U:ℕ→ℕ)(mono:Monotone cap)(simple:G.Simple){ε:ℝ}(pos:0<ε):
    WilsonOriginalCourseSupplement.Award (WilsonWindowJointPurchase.Together
      (WilsonWindowJointPurchase.Together (@WilsonOriginalCompoundStrip.Filed G (narrowed Q)) (@WilsonOriginalCompoundLodge.Filed G))
      (@WilsonOriginalCompoundVertex.Filed G)) (WilsonEmittedPositionSchool.funded.{u} cap U mono simple pos):=
  WilsonOriginalCompoundVertex.funded (narrowed Q) cap U mono simple pos

end YM.Integration.WilsonOriginalCompoundVertexStrip
