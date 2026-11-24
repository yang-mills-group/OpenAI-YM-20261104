import YM.Integration.WilsonVacuumPreResetCurvatureRegister
import YM.Integration.WilsonVacuumPreResetLiftedRack

/-! The finite signed low-path catalogue. The cutoff is on a raw path
and its genuine length, independent of its signed spatial placement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvatureRack
open Lattice RG Wilson PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Collection Quotes Song Meadow RG01Estimate RG01Estimate.Precise RG01Estimate.Abacus
open WilsonVacuumPreResetCurvatureField WilsonVacuumPreResetCurvatureRegister
open Extra.Iteration
open scoped Classical Topology
variable {G:Gauge}{n:Side}

def code (j:Rows n):ℕ:=(numbering Tags).symm (tag j)

def cut (n:Side)(K:PathData G)(t q:ℕ):Finset ℕ:=
  (((Finset.univ:Finset (Seat n)).product ((Finset.range t).image (numbering Tags))).image
    (fun j=>(number n).symm (enter j.1 j.2))).filter (fun i=>arc K (slot (number n i))≤q)

theorem admitted (K:PathData G)(t q i:ℕ):
    i∈cut n K t q ↔ code (number n i)<t ∧ arc K (slot (number n i))≤q:=by
  classical
  rw [cut,Finset.mem_filter]
  apply and_congr_left
  intro _
  constructor
  · rintro mem
    obtain ⟨⟨x,k⟩,placed,hi⟩:=Finset.mem_image.mp mem
    have loc:=((number n).symm_apply_eq).mp hi
    obtain ⟨l,hl,rfl⟩:=Finset.mem_image.mp (Finset.mem_product.mp placed).2
    rw [←loc]
    unfold code
    rw [(entered x _).2,Equiv.symm_apply_apply]
    exact Finset.mem_range.mp hl
  · intro live
    apply Finset.mem_image.mpr
    refine ⟨(seat (number n i),tag (number n i)),Finset.mem_product.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · exact Finset.mem_image.mpr ⟨code (number n i),Finset.mem_range.mpr live,(numbering Tags).apply_symm_apply _⟩
    · exact (number n).symm_apply_eq.mpr (restore _)

theorem invariant (K:PathData G)(t q:ℕ)(s:Signed)(b:Site n)(i:ℕ):
    walk s b i∈cut n K t q ↔ i∈cut n K t q:=by
  rw [admitted,admitted,atWalk]
  simp only [code,←debit,sameTag]

def held (K:PathData G)(c:Clip)(γ β:ℝ)(π:Finset ℕ)(i:ℕ):Config G n→ℝ:=
  if i∈π then source K c γ β (number n i) else 0

def model (A:Listing G n)(B:BudgetPoint)(K:PathData G)(c:Clip)(σ C γ β:ℝ)(t q:ℕ):Leads G n:=
  ⟨⟨fun i=>strings K B (slot (number n i)), A.hard⟩,source K c γ β ∘ number n,
    held K c γ β (cut n K t q), WilsonVacuumPreResetCurvaturePrice.cost (G:=G) B c σ C γ β⟩

def original (A:Listing G n)(B:BudgetPoint)(K:PathData G)(c:Clip)(σ C γ β:ℝ)(t q:ℕ):
    let M:=model A B K c σ C γ β t q
    Abacus.Rack M.listing (B.B+q) M.pioneers:=by
  intro M
  let π:=cut n K t q
  refine ⟨π,fun i x=>if (M.listing.reg i).site=x then 1 else 0,fun i hi=>if_neg hi,
    fun _ _=>by simp,fun _ _ _=>by split <;> norm_num,?_⟩
  intro i hi x weight
  have origin:(M.listing.reg i).site=x:=by simpa using weight
  rw [←origin]
  let j:=number n i
  have len:arc K (slot j)≤q:=((admitted K t q i).mp hi).2
  change (strings K B (slot j)).support⊆neighbors (B.B+q) (strings K B (slot j)).site
  rw [named j,Meadow.tunesAnchor]
  have h:=Meadow.yarn K B (seat j) (raw (tag j))
  have bound:= (debit j K).trans_le len
  intro y hy
  have close:=(neighbors_mem ..).1 (h hy)
  exact (neighbors_mem ..).2 (close.trans (Nat.add_le_add_left bound _))

end YM.Integration.WilsonVacuumPreResetCurvatureRack
