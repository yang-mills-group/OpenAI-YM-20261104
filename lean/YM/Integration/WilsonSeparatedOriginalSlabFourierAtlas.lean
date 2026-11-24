import YM.Integration.WilsonSeparatedOriginalSlabFourierCharacters
import YM.Integration.WilsonSeparatedOriginalSlabJetReader

/-! One before-period spectrum on the true incoming compact wave restores every deposited signed derivative and gives its fixed-order angular majorant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierAtlas
open Filter Set Function Metric UnitAddTorus Lattice Wilson RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Nuclear
open WilsonSeparatedOriginalSlabFourierLattice WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierRoom WilsonSeparatedOriginalSlabPlaneTest WilsonSeparatedOriginalSlabFourierCharacters
open private entry from YM.Integration.WilsonSeparatedOriginalSlabFourierJets
open scoped Topology BigOperators Classical ContDiff
local notation "Y"=>Cloud (Fin 3)
local notation "K"=>Axes→ℤ

def load (s:Fin 3→ℕ):ℕ:=∑i:Fin 3,(s i+2)

/-- The genuine fixed rank appearing in `WilsonSeparatedOriginalProfileTest.original`. -/
def rank (s:Fin 3→ℕ):ℕ:=load s+4*Fintype.card (Fin 3)

theorem fixed (s:Fin 3→ℕ):WilsonSeparatedOriginalSlabFourierBudget.order Axes (load s)=rank s+1:=by
  simp [WilsonSeparatedOriginalSlabFourierBudget.order,rank,load,Axes,Axis,Nat.add_assoc]

private theorem allowance (s:Fin 3→ℕ)(key:(i:Fin 3)→Letter (s i)):pegs s key Finset.univ.toList≤load s:=
  (pegs_cost s key).trans (Finset.sum_le_sum fun _ _=>Nat.le_add_right ..)

theorem original (s:Fin 3→ℕ)(P cap:ℝ)(hp:0<P)(space:4*cap≤P)(Ψ:Wave (Fin 3))
    (seen:∀y∈tsupport Ψ.val,∀i,‖y i‖≤cap){B:ℝ}(bp:0≤B)(fund:Tall Ψ (rank s+1) 1 B):
    ∃F:C(UnitAddTorus Axes,ℂ),Summable (fun k:K=>‖mFourierCoeff F k‖*height k^load s) ∧
      (∑'k:K,‖mFourierCoeff F k‖*height k^load s)≤bank P (rank s+1) B*WilsonSeparatedOriginalSlabFourierBudget.charge Axes (load s) ∧
      ∀(c:ℝ),c≠0→∀key:(i:Fin 3)→Letter (s i),
        (∀x:Y,1/4+dist (cursor P x) 0<1→HasSum (fun k:K=>mFourierCoeff F k*(perform s key (packet (wire P c k) c)).val x) ((perform s key Ψ).val x)) ∧
        ∃A:ℝ,0≤A ∧ ∀(x:Y)(k:K),‖(perform s key (packet (wire P c k) c)).val x‖≤ A*height k^load s:=by
  let M:=rank s+1
  have smooth:ContDiff ℝ ∞ (lift P Ψ):=(show ContDiff ℝ ∞ Ψ.val from Ψ.property).comp (frame P).contDiff
  have small:(1/4:ℝ)+1/4<1:=by norm_num
  have live:=shape hp space Ψ seen
  have hB:0≤bank P M B:=mul_nonneg (pow_nonneg ((show 0≤(1:ℝ) by norm_num).trans (le_max_left ..)) _) bp
  have low:∀x,‖lift P Ψ x‖≤bank P M B:=fun x=>by simpa only [norm_iteratedFDeriv_zero] using derivative P M bp Ψ fund 0 (Nat.zero_le _) x
  have high:∀x,‖iteratedFDeriv ℝ (WilsonSeparatedOriginalSlabFourierBudget.order Axes (load s)) (lift P Ψ) x‖≤bank P M B:=by
    rw [fixed]; exact derivative P M bp Ψ fund M le_rfl
  let F:=WilsonSeparatedOriginalSlabCompactFourier.profile smooth small live
  obtain ⟨fin,bill,_⟩:=WilsonSeparatedOriginalSlabCompactFourier.original smooth small live (load s) hB low high
  refine ⟨F,fin,bill,?_⟩;intro c cp key
  let m:=pegs s key Finset.univ.toList
  have afford:m≤load s:=allowance s key
  obtain ⟨priced,observe⟩:=WilsonSeparatedOriginalSlabJetReader.original s key
  have representation (k:K):(packet (wire P c k) c).val=WilsonSeparatedOriginalSlabFourierJets.wave (cursor P) k:=funext (WilsonSeparatedOriginalSlabFourierCharacters.original P cp k)
  constructor
  · intro x here
    have series:=WilsonSeparatedOriginalSlabFourierJets.original (cursor P) smooth small live (load s) hB low high m afford x here
    have returned:(lift P Ψ ∘ cursor P)=Ψ.val:=funext fun y=>congrArg Ψ.val (physical hp y)
    rw [returned] at series
    have paid:=priced.hasSum series
    rw [observe Ψ x]
    apply paid.congr_fun
    intro k
    symm
    change priced (iteratedFDeriv ℝ m (mFourierCoeff F k • WilsonSeparatedOriginalSlabFourierJets.wave (cursor P) k) x)=_
    rw [←representation,iteratedFDeriv_const_smul_apply (a:=mFourierCoeff F k) (lit (packet (wire P c k) c) m).contDiffAt,map_smul,←observe];rfl
  · refine ⟨‖priced‖*((2*Real.pi)^m*‖cursor P‖^m),mul_nonneg priced.opNorm_nonneg (by positivity),?_⟩
    intro x k
    rw [observe,representation]
    have budget:=entry (cursor P) k m (1:ℂ) x
    simp only [one_smul,norm_one,one_mul] at budget
    refine (priced.le_opNorm _).trans ?_
    calc
      _≤‖priced‖*(((2*Real.pi)^m*‖cursor P‖^m)*height k^m):=mul_le_mul_of_nonneg_left budget priced.opNorm_nonneg
      _≤ _:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (active k) afford) (mul_nonneg priced.opNorm_nonneg (by positivity))

end YM.Integration.WilsonSeparatedOriginalSlabFourierAtlas
