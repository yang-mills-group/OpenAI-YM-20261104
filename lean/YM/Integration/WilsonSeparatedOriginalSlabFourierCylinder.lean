import YM.Integration.WilsonSeparatedOriginalSlabFourierWeights
import YM.Integration.WilsonSeparatedOriginalReplicaExperiments

/-! The complete physical ultraviolet cylinder, with independent fine children and arbitrary held gauges, has one addressed Fourier source before all cutoffs. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierCylinder
open Function Set UnitAddTorus Lattice Wilson Source RG PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Address RG05Readout.Nuclear
open WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierRoom WilsonSeparatedOriginalSlabPlaneTest WilsonSeparatedOriginalSlabFourierCharacters
open WilsonSeparatedOriginalSlabReplicaFilm WilsonSeparatedOriginalSlabReplicaStencil WilsonSeparatedOriginalSlabFourierLattice WilsonSeparatedOriginalSlabFourierAtlas
open scoped Topology BigOperators Classical
local notation "I"=>Fin 3
local notation "K"=>Axes→ℤ
variable {G:Gauge}(R:Run G){b N per:ℕ}(s:I→ℕ)(v:(i:I)→Palette R.family (s i))(h:b≤N)
local notation "Parents"=>I → Site ((R.family).side b per)
local notation "Sites"=>I → Site (((R.family).S.toDepth h per).count)
local notation "Letters"=>(i:I)→Mark (R.family) (s i)
local notation "Space"=>I → Config G ((R.family).side N per)

def restricted (J:ℕ)(Ψ:Wave I)(r:ℝ)(g:Body)(m:ℕ):C(Space,ℂ):=
  premiums (R.family) s m b r • ∑o∈Pulse.area (C:=R.family) (b:=b) (p:=per) J,film s v o h Ψ r g

theorem selected {r cap:ℝ}(rp:0<r)(Ψ:Wave I)(shape:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(g:Body)(m:ℕ):
    restricted R (per:=per) s v h (WilsonSeparatedOriginalSlabActiveWeights.range (R.family) b r cap) Ψ r g m=
      WilsonSeparatedOriginalReplicaExperiments.assembled R (per:=per) s v h Ψ r g m:=by
  unfold restricted WilsonSeparatedOriginalReplicaExperiments.assembled
  apply congrArg (premiums (R.family) s m b r • ·)
  change (∑o∈_,film s v o h Ψ r g)=∑o:Parents,film s v o h Ψ r g
  apply Finset.sum_subset (Finset.subset_univ _);intro o _ ho
  rw [deposited]
  exact Finset.sum_eq_zero fun t _=>Finset.sum_eq_zero fun a _=>by rw [WilsonSeparatedOriginalSlabActiveWeights.original s o h rp Ψ shape ho t a g,zero_smul]

theorem cut (J:ℕ){r cap:ℝ}(Ψ:Wave I){F:C(UnitAddTorus Axes,ℂ)}(received:WilsonSeparatedOriginalSlabFourierWeights.Received (R.family) b J s r cap Ψ F)(g:Body)(m:ℕ):
    HasSum (fun k:K=>mFourierCoeff F k • restricted R (per:=per) s v h J (packet (wire (edge (R.family) b J r cap) (r/(R.family).S.a b) k) (r/(R.family).S.a b)) r g m) (restricted R (per:=per) s v h J Ψ r g m):=by
  let f(k:K):=packet (wire (edge (R.family) b J r cap) (r/(R.family).S.a b) k) (r/(R.family).S.a b)
  have one (o:Parents)(ho:o∈Pulse.area J):HasSum (fun k:K=>mFourierCoeff F k • film s v o h (f k) r g) (film s v o h Ψ r g):=by
    simp only [deposited,Finset.smul_sum,smul_smul]
    exact hasSum_sum (fun t _=>hasSum_sum (fun a _=>(received N per h o ho t a g).smul_const (cell s v o h t a)))
  have whole:HasSum (fun k:K=>∑o∈Pulse.area (C:=R.family) (b:=b) (p:=per) J,mFourierCoeff F k • film s v o h (f k) r g) (∑o∈Pulse.area (C:=R.family) (b:=b) (p:=per) J,film s v o h Ψ r g):=hasSum_sum one
  simpa only [restricted,Finset.smul_sum,smul_comm (mFourierCoeff F _)] using whole.const_smul (premiums (R.family) s m b r)

theorem original (b:ℕ){r cap:ℝ}(rp:0<r)(cp:0≤cap)(Ψ:Wave I)(seen:∀y∈tsupport Ψ.val,∀i,‖y i‖≤cap){B:ℝ}(bp:0≤B)(fund:Tall Ψ (rank s+1) 1 B):
    let J:=WilsonSeparatedOriginalSlabActiveWeights.range (R.family) b r cap
    let P:=edge (R.family) b J r cap
    ∃F:C(UnitAddTorus Axes,ℂ),Summable (fun k:K=>‖mFourierCoeff F k‖*height k^load s) ∧
      (∑'k:K,‖mFourierCoeff F k‖*height k^load s)≤bank P (rank s+1) B*WilsonSeparatedOriginalSlabFourierBudget.charge Axes (load s) ∧
      ∀(N per:ℕ)(h:b≤N)(v:(i:I)→Palette (R.family) (s i))(g:Body)(m:ℕ),
        HasSum (fun k:K=>mFourierCoeff F k • restricted R (per:=per) s v h J (packet (wire P (r/(R.family).S.a b) k) (r/(R.family).S.a b)) r g m)
          (WilsonSeparatedOriginalReplicaExperiments.assembled R (per:=per) s v h Ψ r g m):=by
  intro J P
  obtain ⟨F,law,bill,read⟩:=WilsonSeparatedOriginalSlabFourierWeights.original (R.family) b J s r cap Ψ rp cp seen bp fund
  refine ⟨F,law,bill,?_⟩;intro N per h v g m
  rw [←selected R s v h rp Ψ seen g m]
  exact cut R s v h J Ψ read g m

end YM.Integration.WilsonSeparatedOriginalSlabFourierCylinder
