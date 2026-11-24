import YM.Integration.WilsonSeparatedOriginalSlabFourierIntegral

/-! The same preperiod spectrum recovers each complete addressed center integral, including every independent child residue and actual signed derivative letter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierWeights
open Function Set MeasureTheory UnitAddTorus Lattice Wilson Source RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Pulse RG05Readout.Flatten RG05Readout.Nuclear
open WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierRoom WilsonSeparatedOriginalSlabPlaneTest WilsonSeparatedOriginalSlabFourierCharacters
open WilsonSeparatedOriginalSlabReplicaStencil WilsonSeparatedOriginalSlabFourierLattice WilsonSeparatedOriginalSlabFourierAtlas
open private location located coefficient stamp exposed from YM.Integration.WilsonSeparatedOriginalReplicaRegularity
open scoped BigOperators Classical Topology ContDiff
local notation "I"=>Fin 3
local notation "K"=>Axes→ℤ
variable {G:Gauge}(C:Family G)(b J:ℕ)(s:I→ℕ)(r cap:ℝ)(Ψ:Wave I)

def Received (F:C(UnitAddTorus Axes,ℂ)):Prop:=∀(N per:ℕ)(h:b≤N)(o:I→Site (C.side b per)), o∈Pulse.area J →
  ∀(t:I→Site (C.S.toDepth h per).count)(a:(i:I)→Mark C (s i))(g:Body),
    HasSum (fun k:K=>mFourierCoeff F k * weight s o h r t a g (packet (wire (edge C b J r cap) (r/C.S.a b) k) (r/C.S.a b))) (weight s o h r t a g Ψ)

theorem original (rp:0<r)(cp:0≤cap)(shape:∀y∈tsupport Ψ.val,∀i,‖y i‖≤cap){B:ℝ}(bp:0≤B)(fund:Tall Ψ (rank s+1) 1 B):
    ∃F:C(UnitAddTorus Axes,ℂ),Summable (fun k:K=>‖mFourierCoeff F k‖*height k^load s) ∧
      (∑'k:K,‖mFourierCoeff F k‖*height k^load s)≤bank (edge C b J r cap) (rank s+1) B*WilsonSeparatedOriginalSlabFourierBudget.charge Axes (load s) ∧ Received C b J s r cap Ψ F:=by
  let P:=edge C b J r cap
  obtain ⟨hp,enough,_⟩:=room C b J rp cp
  obtain ⟨F,money,payment,jets⟩:=WilsonSeparatedOriginalSlabFourierAtlas.original s P cap hp enough Ψ shape bp fund
  refine ⟨F,money,payment,?_⟩
  intro N per h o ho t a g
  let A:=C.S.toDepth h per
  let keys (i:I):Letter (s i):=(a i).1
  let scale:=r/C.S.a b
  let β:ℂ:=(∏i,ratioX A (s i))*((((r⁻¹*C.S.a b)*(A.count.val:ℝ)⁻¹):ℝ):ℂ)^pegs s keys Finset.univ.toList
  let profile (k:K):=packet (wire P scale k) scale
  have raw (f:Wave I)(z:E4):atSite s o h r t z a f=β*(perform s keys f).val (location o h r t z):=by
    change coefficient s o h f r t z a=_
    rw [coefficient,exposed];unfold β;ring
  obtain ⟨point,⟨A₀,_,bounds⟩⟩:=jets scale (div_pos rp (C.S.a_pos b)).ne' keys
  apply WilsonSeparatedOriginalSlabFourierIntegral.purchased (c:=mFourierCoeff F) (cost:=fun k=>height k^load s) (H:=fun k z=>atSite s o h r t z a (profile k)) (F:=fun z=>atSite s o h r t z a Ψ) (A:=‖β‖*A₀) _ money
  · intro k;simp_rw [raw];exact continuous_const.mul ((lit (perform s keys (profile k)) 0).continuous.comp (located o h r t))
  · intro k z;rw [raw,norm_mul,mul_assoc];exact mul_le_mul_of_nonneg_left (bounds _ k) (norm_nonneg β)
  · intro z hz;simp_rw [raw]
    have signed:HasSum (fun k:K=>mFourierCoeff F k*(perform s keys (profile k)).val (location o h r t z)) ((perform s keys Ψ).val (location o h r t z)):=point _ (central J o ho h rp cp t hz)
    simpa only [mul_left_comm β] using signed.mul_left β

end YM.Integration.WilsonSeparatedOriginalSlabFourierWeights
