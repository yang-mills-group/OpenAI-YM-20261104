import YM.Integration.WilsonLocalPlaquetteAction

/-! Each oriented physical bond has at most six plaquette incidences,
with multiplicities retained even on the smallest periodic lattice. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteMultiplicity
open Function Finset Lattice Wilson RG WilsonPlaquetteIncidence WilsonLocalPlaquetteField
open scoped Classical BigOperators
variable {n:Side}

def orientation (a:PlaqAxes) : Fin 4→Axis := ![a.val.1,a.val.2,a.val.1,a.val.2]

theorem axis (q:Face (Per n)) (j:Fin 4) : (edges q j).2=orientation q.2 j := by fin_cases j <;> rfl

theorem unique (a:PlaqAxes) (j:Fin 4) : Injective fun x:Site n=>edges (x,a) j := by
  intro x y h
  have eq:=congrArg Prod.fst h
  fin_cases j
  · exact eq
  · exact add_right_cancel eq
  · exact add_right_cancel eq
  · exact eq

def tickets (k:Axis) : Finset (PlaqAxes×Fin 4) := univ.filter fun p=>orientation p.1 p.2=k

theorem six (k:Axis) : (tickets k).card=6 := by fin_cases k <;> decide

theorem atMost (e:Bonds n) : Fintype.card {p:Face (Per n)×Fin 4 // edges p.1 p.2=e}≤6 := by
  let key (p:{p:Face (Per n)×Fin 4 // edges p.1 p.2=e}) : ↥(tickets e.2) :=
    ⟨(p.val.1.2,p.val.2),mem_filter.mpr ⟨mem_univ _,(axis _ _).symm.trans (congrArg Prod.snd p.property)⟩⟩
  have inj : Injective key := by
    rintro ⟨⟨⟨x,a⟩,j⟩,hx⟩ ⟨⟨⟨y,b⟩,l⟩,hy⟩ h
    have hkl : (a,j)=(b,l) := congrArg Subtype.val h
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj hkl
    have hxy:=unique a j (hx.trans hy.symm)
    subst y;rfl
  simpa only [Fintype.card_coe,six] using Fintype.card_le_of_injective key inj

theorem sum (h:Bonds n→ℝ) (pos:∀i,0≤h i) :
    (∑q:Face (Per n),∑j:Fin 4,h (edges q j))≤6*∑e:Bonds n,h e := by
  let locate (p:Face (Per n)×Fin 4):=edges p.1 p.2
  change (∑q:Face (Per n),∑j:Fin 4,h (locate (q,j)))≤_
  rw [← Fintype.sum_prod_type (fun p:Face (Per n)×Fin 4=>h (locate p)),← Fintype.sum_fiberwise' locate h,Finset.mul_sum]
  apply sum_le_sum;intro e _
  simp only [sum_const,card_univ,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (pos e)
  exact_mod_cast atMost e

end YM.Integration.WilsonLocalPlaquetteMultiplicity
