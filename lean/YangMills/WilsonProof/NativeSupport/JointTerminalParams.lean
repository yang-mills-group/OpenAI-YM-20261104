import YangMills.WilsonProof.NativeSupport.JointStageWord
import YangMills.WilsonProof.NativeSupport.JointTerminalDirection
import Mathlib.Analysis.Complex.RealDeriv

/-! Physical source subsets, the common kinetic fugacity, and the derivative
of the original normalized real evaluations on the identity component. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Dated
open Function Finset Lattice RG Wilson Marker Packet JointShadow
open scoped Classical BigOperators
variable {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] {t N:ℕ} {n:Side}
local notation "V₀" => Names I t N n

def phys (E:Finset I):Finset (Names I t N n):=E.map ⟨Sum.inl,Sum.inl_injective⟩
def other : Finset (Names I t N n):=(phys (t:=t) (N:=N) (n:=n) (univ:Finset I))ᶜ
def moving : Finset (Names I t N n):=univ.filter (Sum.elim (fun _=>False) (fun q=>q.1.2=true))

theorem open_subset (u:V→ℂ) (A:Finset V) (P:Poly (Stock.census V)):
    openAt (fun i=>if i∈A then u i else 0) P=∑ s∈A.powerset,(∏ i∈s,u i)*P.part (tag s) := by
  unfold openAt
  rw [←sum_subset (subset_univ A.powerset) (f:=fun s=>(∏ i∈s,if i∈A then u i else 0)*P.part (tag s))]
  · apply sum_congr rfl;intro s hs
    congr 1;apply prod_congr rfl;intro i hi;rw [if_pos (mem_powerset.mp hs hi)]
  · intro s _ gone
    obtain ⟨i,hi,miss⟩:=not_subset.mp (fun sub=>gone (mem_powerset.mpr sub))
    rw [prod_eq_zero hi (if_neg miss),zero_mul]

theorem outside (E:Finset I):Disjoint (other:Finset V₀) (phys E) := by
  apply disjoint_left.mpr
  intro i x y
  obtain ⟨v,hv,rfl⟩:=mem_map.mp y
  exact (mem_compl.mp x) (mem_map.mpr ⟨v,mem_univ _,rfl⟩)

theorem encoded (E:Finset I) (z:ℂ) (P:Poly (Stock.census V₀)):
    openAt (params E z) P=TerminalGas.evaluated moving (other∪phys E) P z := by
  let A:Finset V₀:=other∪phys E
  have assignment : params (t:=t) (N:=N) (n:=n) E z=fun i=>if i∈A then TerminalGas.fugacity moving z i else 0 := by
    funext i
    rcases i with i|⟨⟨j,k⟩,b⟩
    · by_cases hit:i∈E <;> simp [A,params,other,phys,moving,TerminalGas.fugacity,hit]
    · cases k <;> simp [A,params,other,phys,moving,TerminalGas.fugacity]
  rw [assignment,open_subset]
  unfold TerminalGas.evaluated TerminalGas.sliceZ
  apply sum_congr rfl;intro s _
  rw [on_part]

theorem real_derivative {f g:ℂ→ℂ} {a b:ℂ} (hf:HasDerivAt f a 0) (hg:HasDerivAt g b 0)
    (same:∀ x:ℝ,f (x:ℂ)=g (x:ℂ)):a=b := by
  have h₁:HasDerivAt (fun x:ℝ=>f (x:ℂ)) a 0:=hf.comp_ofReal
  have h₂:HasDerivAt (fun x:ℝ=>g (x:ℂ)) b 0:=hg.comp_ofReal
  rw [show (fun x:ℝ=>f (x:ℂ))=(fun x:ℝ=>g (x:ℂ)) from funext same] at h₁
  exact h₁.unique h₂

end YM.Integration.InletSusceptibility.Dated
