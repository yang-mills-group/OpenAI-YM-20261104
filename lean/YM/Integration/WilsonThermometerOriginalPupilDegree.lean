import YM.Integration.WilsonThermometerOriginalDepositedSlope

/-! A numerical finite pupil is a polynomial of bounded field degree on every occupied copy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalPupilDegree
open Function Finset Lattice RG Marker Multi Comparison.RG02 Comparison.RG02.Valence
open FVA1Physical.Wilson Exterior QuadraticLocal.Earn QuadraticLocal.Sunrise FVA1Physical.TwoReset
open scoped BigOperators Classical ContDiff

variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private theorem monomial {I:Type*} (T:Finset I) (f:I→E→ℂ) (h:∀i,Level 1 (f i)) :
    Level (T.card:ℤ) (fun x=>∏i∈T,f i x) := by
  induction T using Finset.induction_on with
  | empty=>simp only [card_empty,Nat.cast_zero,prod_empty]; exact Level.constant 1
  | @insert a t fresh ih=>
    simp only [card_insert_of_notMem fresh,Nat.cast_add,Nat.cast_one,prod_insert fresh]
    simpa only [add_comm (t.card:ℤ) 1] using (h a).mul ih

private theorem diagonal [FiniteDimensional ℝ E] {d:ℕ} (K:Tensor.T E ℂ d) :
    Level (d:ℤ) (Tensor.diagonal K) := by
  let b:=Module.finBasis ℝ E
  let c (j:Fin (Module.finrank ℝ E)):=Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap (b.coord j)
  let T:=K.toMultilinearMap
  have expanded (x:E) : Tensor.diagonal K x=∑ a:Fin d→Fin (Module.finrank ℝ E),
      (T (fun l=>b (a l)))*(∏l,c (a l) x) := by
    change T (fun _=>x)=_
    have repl : (fun _:Fin d=>x) = fun _:Fin d=>∑ j,b.repr x j • b j :=
      funext fun _=>(b.sum_repr x).symm
    rw [repl]
    rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]
    apply Finset.sum_congr rfl
    intro a _
    rw [T.map_smul_univ]
    simp [c,Complex.real_smul,Complex.ofReal_prod,mul_comm]
  simp_rw [show Tensor.diagonal K=(fun x=>∑ a:Fin d→Fin (Module.finrank ℝ E),
      T (fun l=>b (a l))*(∏l,c (a l) x)) from funext expanded]
  apply Level.total
  intro a _
  have h:=monomial (univ:Finset (Fin d)) (fun l=>c (a l)) (fun l=>Level.linear (c (a l)))
  simpa only [card_univ,Fintype.card_fin] using h.factor (T fun l=>b (a l))

variable {G:Gauge} {V:Type} [DecidableEq V] {R:Census V} {n:Side}

/-- This bound depends on the angular order and the actual pupil's pole, on arbitrary full fields. -/
theorem coefficient (M:Bulk.Colors R G n) (j:ℕ) (s:Multi.Hot R) :
    Level ((M.power s + j:ℕ):ℤ) (fun a:fieldDir G n 1=>(Air.discharge M j a).part s.val) := by
  simp only [Air.discharge,Multi.part_lit]
  have base:=diagonal (Tensor.coeff (Bulk.projected (M.mark s)) (M.power s+j) 0)
  have h:=SignCovariance.affine_degree ((1:ℝ),(0:fieldDir G n 1))
    (ContinuousLinearMap.inr ℝ ℝ (fieldDir G n 1)) base
  simpa [Tensor.diagonal,Tensor.coeff] using h

open AllOrder.Floe Comparison.RG02.Adjacent Comparison.RG02.Assembly

theorem copied {ι α:Type} {f:Side} {J:Passport n V} (mult:n.val∣f.val) (M:ι→Row J R G α)
    (w:V→ℕ) (L:Layout G) (T:Finset Age) (v:α) (j:ℕ) (s:Multi.Hot R) :
    Level ((Launch.index R w s.val+1+j:ℕ):ℤ) (fun a:Stationary.Link G f=>(peek mult M w L T v j a).part s.val) := by
  let X:=copyColor mult M w (fun i=>(M i).paint v) L T
  have bound:=coefficient X j s
  have h:=SignCovariance.affine_degree (0:fieldDir G f 1) (Stationary.arm G f 1).toContinuousLinearMap bound
  change Level ((X.power s+j:ℕ):ℤ) (fun a:Stationary.Link G f=>(Air.discharge X j ((Stationary.arm G f 1) a)).part s.val)
  simpa only [zero_add,ContinuousLinearEquiv.coe_coe] using h

theorem restamped {ι α:Type} {f:Side} {J:Passport n V} (mult:n.val∣f.val) (M:ι→Row J R G α)
    (w:V→ℕ) (L:Layout G) (T:Finset Age) (v:α) (p:ℕ) (K:UnitCost)
    (value:ℕ→Stationary.Link G f→Poly R) (agree:∀d≤p,∀a,value d a=peek mult M w L T v d a)
    (s:Multi.Hot R) (j:ℕ) (hj:j≤p) :
    Level ((Launch.index R w s.val+1+j:ℕ):ℤ) (WilsonOriginalCoverJetColors.reset p value K s j) := by
  let U (d:ℕ) (a:Stationary.Link G f):=(value d a).part s.val
  let degree (d:ℕ):ℤ:=(Launch.index R w s.val+1+d:ℕ)
  have rates:Charge p degree U:=by
    intro d hd
    change Level (degree d) (fun a=>(value d a).part s.val)
    simp_rw [agree d hd]
    exact copied mult M w L T v d s
  have bornDegree:=apportion K 0 p rates j hj (fun l hl=>by dsimp [degree]; omega)
  have h:=SignCovariance.affine_degree (0:Stationary.Link G f) (Stationary.arm G f 1).symm.toContinuousLinearMap
    bornDegree
  change Level (degree j) (fun x:fieldDir G f 1=>born U K 0 p j ((Stationary.arm G f 1).symm x))
  simpa only [zero_add,ContinuousLinearEquiv.coe_coe] using h

/-- Re-inscription on the group retains every booked occupied coefficient before the next
conditional forest or tag is chosen. The vacuum function is the one specified at reception. -/
theorem rendered {ι α:Type} {f:Side} {J:Passport n V} (mult:n.val∣f.val) (M:ι→Row J R G α)
    (w:V→ℕ) (L:Layout G) (T:Finset Age) (v:α) (p:ℕ) (K:UnitCost)
    (value:ℕ→Stationary.Link G f→Poly R) (agree:∀d≤p,∀a,value d a=peek mult M w L T v d a)
    (quiet:ℝ→Wilson.Config G f→ℝ) (s:Multi.Hot R) (j:ℕ) (hj:j≤p) (z:fieldDir G f 1) :
    let X:=WilsonOriginalCoverJetColors.colors quiet (fun u=>Launch.index R w u.val+1) p
      (WilsonOriginalCoverJetColors.reset p value K)
    X.vac=quiet ∧ (Air.discharge X j z).part s.val=WilsonOriginalCoverJetColors.reset p value K s j z := by
  refine ⟨rfl,?_⟩
  have rows:=WilsonOriginalCoverJetColors.angular quiet (fun u:Multi.Hot R=>Launch.index R w u.val+1) p
    (WilsonOriginalCoverJetColors.reset p value K) (restamped mult M w L T v p K value agree) j hj z
  simpa only [Multi.part_lit] using congrArg (fun a:Poly R=>a.part s.val) rows

end YM.Integration.WilsonThermometerOriginalPupilDegree
