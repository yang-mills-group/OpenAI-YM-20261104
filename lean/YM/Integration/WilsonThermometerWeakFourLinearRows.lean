import YM.Integration.WilsonThermometerWeakProjectedSolve
import YM.TraceExtension.Terrace.Insert
import YM.Integration.WilsonThermometerWeakFourMixedRoster
import YM.Integration.WilsonAddressedWeakRootedReading
/-! Linear responses of the measured original two-column detector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFourLinearRows
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat Legato Bandage Cells Next.UVStress RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerWeakPanelBorn WilsonThermometerOwnOffsetField
open Push.RelayDifference
open Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open WilsonAddressedWeakPointCells WilsonAddressedWeakCorrectedCylinder
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) {k N p:ℕ} {D:Deck G}
local notation "C" => R.family

private theorem integrable {N p:ℕ} {f:Config G ((C).side N p)→ℂ} (h:Continuous f):
    Integrable f (law G _ ((C).beta N p)) :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def read (d N p:ℕ) (o:Site ((C).side N p)) (X:Config G ((C).side N p)→ℂ) (test:Continuous X) :
    (C).label d →ₗ[ℂ] ℂ where
  toFun x:=moment ((C).beta N p) (fun U=>(C).O N p x o U*X U)
  map_add' x y:=by
    have linear:=(((C).linearO N p d o).mk' _).map_add x y
    change (C).O N p (x+y) o=(C).O N p x o+(C).O N p y o at linear
    simp only [linear,Pi.add_apply,add_mul,moment]
    exact integral_add (integrable R (((C).continuousO N p d x o).mul test))
      (integrable R (((C).continuousO N p d y o).mul test))
  map_smul' c x:=by
    have linear:=(((C).linearO N p d o).mk' _).map_smul c x
    change (C).O N p (c • x) o=c • (C).O N p x o at linear
    simp only [linear,Pi.smul_apply,smul_eq_mul,mul_assoc,moment,integral_const_mul,RingHom.id_apply]


section
variable {d:ℕ} {I:Type*} [Fintype I]
def stencil (u:I→(C).label d) : (I→ℂ) →ₗ[ℂ] Palette C d :=
  ∑i, (LinearMap.proj i).smulRight (RG05Readout.Address.chunk («C»:=R.family) (primaryLetter d) (u i))

theorem entries (u:I→(C).label d) (t:I→ℂ) :
    stencil R u t=∑i,t i • (RG05Readout.Address.chunk («C»:=R.family) (primaryLetter d) (u i)) := by
  simp [stencil,LinearMap.sum_apply,LinearMap.smulRight_apply]

theorem tariff (u:I→(C).label d) (t:I→ℂ) :
    size (stencil R u t) ≤ ‖t‖*∑i,((C).labels.level d).coeffSize (u i) := by
  rw [entries,Finset.mul_sum]
  refine (size_sum _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  rw [size_smul,size_chunk]
  exact mul_le_mul_of_nonneg_right (norm_le_pi_norm t i) (Work.G08.size_nonneg _ _)

def entrance (Q:Emblems C d) (live:k≤N) : Palette C d →ₗ[ℂ] (C).label d where
  toFun y := (((C).S.a k:ℂ)^d) • ((C).factory d N p).terminal (finer Q live y (primaryLetter d))
  map_add' x y := by
    simp only [map_add,Pi.add_apply]
    exact (congrArg ((((C).S.a k:ℂ)^d) • ·) (((C).factory d N p).terminal.map_add
      (finer Q live x (primaryLetter d)) (finer Q live y (primaryLetter d)))).trans (smul_add _ _ _)
  map_smul' a y := by
    simp only [map_smul,Pi.smul_apply,RingHom.id_apply]
    exact (congrArg ((((C).S.a k:ℂ)^d) • ·) (((C).factory d N p).terminal.map_smul a
      (finer Q live y (primaryLetter d)))).trans (smul_comm _ _ _)

def panel (Q:Emblems C d) (live:k≤N) (u:I→(C).label d) : (I→ℂ) →ₗ[ℂ] (C).label d :=
  (entrance R (p:=p) Q live).comp (stencil R u)


end

def gram (z:Fin 2→Site ((C).side N p)) (r:Fin 2→Emblems C 4) (hk:k≤N)
    (u:Fin 2→Glyph D 4→(C).label 4):Matrix (Glyph D 4) (Glyph D 4) ℂ:=
  fun a e=>reading R (fun _=>4) z (fun i=>chunk («C»:=R.family) (primaryLetter 4) (u i (![a,e] i))) r hk full

theorem arm_field (r:Emblems C 4) (hk:k≤N) (u:(C).label 4) (z:Site ((C).side N p)):
    (C).O N p (entrance R (p:=p) r hk (chunk («C»:=R.family) (primaryLetter 4) u)) z=arm R r hk z u:=by
  let a:ℂ:=((C).S.a k:ℂ)^4
  let e:=(C).factory 4 N p |>.terminal (finer r hk (chunk («C»:=R.family) (primaryLetter 4) u) (primaryLetter 4))
  exact (((C).linearO N p 4 z).mk' _).map_smul a e

theorem continuous (r:Emblems C 4) (hk:k≤N) (z:Site ((C).side N p)) (u:(C).label 4):
    Continuous (arm R r hk z u):=by
  rw [←arm_field]
  exact (C).continuousO N p 4 _ _

theorem entry (z:Fin 2→Site ((C).side N p)) (r:Fin 2→Emblems C 4) (hk:k≤N)
    (u:Fin 2→Glyph D 4→(C).label 4) (a e:Glyph D 4):
    read R 4 N p (z 0) (arm R (r 1) hk (z 1) (u 1 e)) (continuous R ..)
      (entrance R (p:=p) (r 0) hk (chunk («C»:=R.family) (primaryLetter 4) (u 0 a)))=gram R z r hk u a e:=by
  unfold gram
  rw [WilsonAddressedWeakRootedReading.measured]
  change moment ((C).beta N p) (fun U=>(C).O N p _ (z 0) U*arm R (r 1) hk (z 1) (u 1 e) U)=
    moment ((C).beta N p) (fun U=>∏i:Fin 2,WilsonThermometerIntrinsicRoster.source R _ z _ r hk i U)
  rw [arm_field]
  congr 1
  funext U
  rw [Fin.prod_univ_two]
  rfl

theorem rows (z:Fin 2→Site ((C).side N p)) (r:Fin 2→Emblems C 4) (hk:k≤N)
    (u:Fin 2→Glyph D 4→(C).label 4) (t:Glyph D 4→ℂ) (e:Glyph D 4):
    read R 4 N p (z 0) (arm R (r 1) hk (z 1) (u 1 e)) (continuous R ..)
      (panel R (p:=p) (r 0) hk (u 0) t)=(t ᵥ* gram R z r hk u) e:=by
  rw [panel,LinearMap.comp_apply,entries]
  simp only [map_sum,map_smul,smul_eq_mul,Matrix.vecMul,dotProduct]
  apply Finset.sum_congr rfl
  intro a _
  rw [WilsonThermometerWeakFourLinearRows.entry]

def inverseBill (K:Matrix (Glyph D 4) (Glyph D 4) ℂ):ℝ:=1+∑a,∑e,‖K⁻¹ a e‖
theorem fee (A K:Matrix (Glyph D 4) (Glyph D 4) ℂ) (near:∀i j,‖A⁻¹ i j-K⁻¹ i j‖<1):
    ∀i j,‖A⁻¹ i j‖ ≤ inverseBill K:=by
  intro i j
  have one:‖K⁻¹ i j‖≤∑c,‖K⁻¹ i c‖:=Finset.single_le_sum (fun c _=>norm_nonneg (K⁻¹ i c)) (Finset.mem_univ j)
  have two:(∑c,‖K⁻¹ i c‖)≤∑b,∑c,‖K⁻¹ b c‖:=Finset.single_le_sum (fun b _=>Finset.sum_nonneg (fun c _=>norm_nonneg (K⁻¹ b c))) (Finset.mem_univ i)
  have bound:=norm_le_norm_sub_add (A⁻¹ i j) (K⁻¹ i j)
  unfold inverseBill
  linarith only [bound,near i j,one,two]

variable (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    {P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)} (b:Presentation R.family)
    (house:Hearthside R.family V W P b (PhysicalNext.Repeat.Legato.Bandage.fly R.alloy.B.a))

include V W b house

theorem faithful (simple:G.Simple) (N p:ℕ): Injective (b.step 4 (N,p)):=by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have zero:x∈(b.step 4 (N,p)).toLinearMap.ker:=hx
  rw [(house.foundation.step 4 N p).ker] at zero
  obtain ⟨v,hv,eq⟩:=zero
  rw [Trace.Terrace.immune4 simple hv,map_zero] at eq
  exact eq.symm

theorem earned (simple:G.Simple)
    (z:Fin 2→Site ((C).side N p)) (r:Fin 2→Emblems C 4) (hk:k≤N)
    (u:Fin 2→Glyph D 4→(C).label 4) (K:Matrix (Glyph D 4) (Glyph D 4) ℂ)
    (inv:IsUnit (gram R z r hk u)) (near:∀i j,‖(gram R z r hk u)⁻¹ i j-K⁻¹ i j‖<1)
    (x:(C).label 4) (q:ℝ) (hq:0≤q)
    (wage:∀a,‖moment ((C).beta N p) (fun U=>(C).O N p x (z 0) U*arm R (r 1) hk (z 1) (u 1 a) U)‖≤q):
    ∃y:Palette C 4, (((C).S.a k:ℂ)^4) • ((C).factory 4 N p).terminal (finer (r 0) hk y (primaryLetter 4))=x ∧
      size y≤((Fintype.card (Glyph D 4):ℝ)*inverseBill K*q)*∑i,((C).labels.level 4).coeffSize (u 0 i):=by
  let L:=LinearMap.pi fun e=>read R 4 N p (z 0) (arm R (r 1) hk (z 1) (u 1 e)) (continuous R ..)
  let E:=panel R (p:=p) (r 0) hk (u 0)
  let A:=gram R z r hk u
  let J:ℝ:=(Fintype.card (Glyph D 4):ℝ)*inverseBill K
  have posI:0 ≤ inverseBill K:=by unfold inverseBill;positivity
  have posJ:0≤J:=by dsimp only [J];positivity
  have readE (t:Glyph D 4→ℂ):L (E t)=t ᵥ* A:=funext (rows R z r hk u t)
  have recover (t:Glyph D 4→ℂ):‖t‖≤J*‖L (E t)‖:=by
    rw [readE]
    exact WilsonThermometerWeakProjectedSolve.inverse_bound A inv _ posI (fee _ K near) t
  have cash:‖L x‖≤q:=(pi_norm_le_iff_of_nonneg hq).2 wage
  obtain ⟨t,same,_⟩:=WilsonThermometerWeakProjectedSolve.original (C) D 4 V W b house (N,p)
    E L A readE inv (inverseBill K) posI (fee _ K near) x 0 0 0 q cash
    (by intro t hz;have zero:E t=0:=faithful R V W b house simple N p (hz.trans (map_zero _).symm);simp [zero])
    (by intro t hz;rw [faithful R V W b house simple N p hz,sub_self,norm_zero];simp)
    (by simp)
  have literal:E t=x:=faithful R V W b house simple N p same
  have sizeT:=recover t
  rw [literal] at sizeT
  exact ⟨stencil R (u 0) t,literal,(tariff R (u 0) t).trans (mul_le_mul_of_nonneg_right
    (sizeT.trans (mul_le_mul_of_nonneg_left cash posJ)) (Finset.sum_nonneg fun i _=>Work.G08.size_nonneg _ _))⟩
end YM.Integration.WilsonThermometerWeakFourLinearRows
end
