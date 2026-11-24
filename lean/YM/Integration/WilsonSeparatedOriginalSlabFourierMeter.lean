import YM.Integration.WilsonSeparatedOriginalSlabFourierCylinder

/-! Any linear Wilson reading of these original finite cylinders inherits the same Fourier identity.  The common range is a finite span before the reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierMeter
open Function Set UnitAddTorus Lattice Wilson Source RG PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Address RG05Readout.Nuclear
open WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierRoom WilsonSeparatedOriginalSlabPlaneTest WilsonSeparatedOriginalSlabFourierCharacters
open WilsonSeparatedOriginalSlabReplicaFilm WilsonSeparatedOriginalSlabReplicaStencil WilsonSeparatedOriginalSlabFourierLattice WilsonSeparatedOriginalSlabFourierAtlas WilsonSeparatedOriginalSlabFourierCylinder
open scoped Topology BigOperators Classical
local notation "I"=>Fin 3
local notation "K"=>Axes→ℤ
variable {G:Gauge}(R:Run G){b N per:ℕ}(s:I→ℕ)(v:(i:I)→Palette R.family (s i))(h:b≤N)
local notation "Parents"=>I → Site (R.family.side b per)
local notation "Space"=>I → Config G (R.family.side N per)

theorem cut (J:ℕ){r cap:ℝ}(Ψ:Wave I){F:C(UnitAddTorus Axes,ℂ)}(received:WilsonSeparatedOriginalSlabFourierWeights.Received R.family b J s r cap Ψ F)(g:Body)(m:ℕ)(meter:C(Space,ℂ)→ₗ[ℂ]ℂ):
    HasSum (fun k:K=>mFourierCoeff F k * meter (restricted R (per:=per) s v h J (packet (wire (edge R.family b J r cap) (r/R.family.S.a b) k) (r/R.family.S.a b)) r g m)) (meter (restricted R (per:=per) s v h J Ψ r g m)):=by
  let f(k:K):=packet (wire (edge R.family b J r cap) (r/R.family.S.a b) k) (r/R.family.S.a b)
  have one (o:Parents)(ho:o∈Pulse.area J):HasSum (fun k:K=>mFourierCoeff F k * meter (film s v o h (f k) r g)) (meter (film s v o h Ψ r g)):=by
    simp only [deposited,map_sum,map_smul,smul_eq_mul,Finset.mul_sum,←mul_assoc]
    exact hasSum_sum (fun t _=>hasSum_sum (fun a _=>(received N per h o ho t a g).mul_right (meter (cell s v o h t a))))
  have whole:HasSum (fun k:K=>∑o∈Pulse.area (C:=R.family) (b:=b) (p:=per) J,mFourierCoeff F k * meter (film s v o h (f k) r g)) (∑o∈Pulse.area (C:=R.family) (b:=b) (p:=per) J,meter (film s v o h Ψ r g)):=hasSum_sum one
  simpa only [restricted,map_smul,map_sum,smul_eq_mul,Finset.mul_sum,mul_left_comm (mFourierCoeff F _)] using whole.mul_left (premiums R.family s m b r)

theorem original (b J:ℕ){r cap:ℝ}(rp:0<r)(cp:0≤cap)(Ψ:Wave I)(seen:∀y∈tsupport Ψ.val,∀i,‖y i‖≤cap){B:ℝ}(bp:0≤B)(fund:Tall Ψ (rank s+1) 1 B):
    let P:=edge R.family b J r cap
    ∃F:C(UnitAddTorus Axes,ℂ),Summable (fun k:K=>‖mFourierCoeff F k‖*height k^load s) ∧
      (∑'k:K,‖mFourierCoeff F k‖*height k^load s)≤bank P (rank s+1) B*WilsonSeparatedOriginalSlabFourierBudget.charge Axes (load s) ∧
      ∀(N per:ℕ)(h:b≤N)(v:(i:I)→Palette R.family (s i))(g:Body)(m:ℕ)(meter:C(I → Config G (R.family.side N per),ℂ)→ₗ[ℂ]ℂ),
        HasSum (fun k:K=>mFourierCoeff F k *meter (restricted R (per:=per) s v h J (packet (wire P (r/R.family.S.a b) k) (r/R.family.S.a b)) r g m)) (meter (restricted R (per:=per) s v h J Ψ r g m)):=by
  intro P
  obtain ⟨F,law,bill,read⟩:=WilsonSeparatedOriginalSlabFourierWeights.original R.family b J s r cap Ψ rp cp seen bp fund
  exact ⟨F,law,bill,fun N per h v g m meter=>cut R s v h J Ψ read g m meter⟩

end YM.Integration.WilsonSeparatedOriginalSlabFourierMeter
