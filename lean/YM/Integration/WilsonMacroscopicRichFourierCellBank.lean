import YM.Integration.WilsonMacroscopicRichFourierCounterterm
import YM.Integration.WilsonMacroscopicRichSignedBookingSplit

/-! Finite weight coordinates for the original three upper entries, with every
parent, child residue, and derivative letter. The cycle and all its prices are
fixed before the regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFourierCellBank
open Function Set UnitAddTorus Lattice Wilson RG Source PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten RG05Readout.Nuclear
open WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierRoom WilsonSeparatedOriginalSlabPlaneTest
open WilsonSeparatedOriginalSlabFourierCharacters WilsonSeparatedOriginalSlabFourierLattice WilsonSeparatedOriginalSlabFourierAtlas
open WilsonSeparatedOriginalSlabFourierCylinder WilsonSeparatedOriginalSlabReplicaStencil WilsonSeparatedOriginalSlabReplicaFilm
open WilsonSeparatedOriginalSlabFourierCredit
open scoped Topology BigOperators Classical
local notation "I"=>Fin 3
local notation "K"=>Axes→ℤ
variable {G:Gauge} (R:Run G) {b N p:ℕ} (s:I→ℕ) (h:b≤N)
local notation "C₀"=>R.family
local notation "Upper"=>Config G ((C₀).side N p)
local notation "Parents"=>I→Site ((C₀).side b p)
local notation "Children"=>I→Site ((C₀).S.toDepth h p).count
local notation "Bids"=>(i:I)→Mark C₀ (s i)
abbrev Index (p:ℕ):= (I→Site ((C₀).side b p)) × (I→Site ((C₀).S.toDepth h p).count) × ((i:I)→Mark C₀ (s i))

def weights (J:ℕ)(r:ℝ)(g:Body)(Ψ:Wave I) (x:Index R s h p):ℂ :=
  if x.1∈Pulse.area (C:=C₀) (b:=b) (p:=p) J then weight s x.1 h r x.2.1 x.2.2 g Ψ else 0

def upper (v:(i:I)→Palette C₀ (s i))(J:ℕ)(r:ℝ)(m:ℕ) :
    (Index R s h p→ℂ)→ₗ[ℂ]C(I→Upper,ℂ) where
  toFun z:=(premiums C₀ s m b r) • ∑ o∈Pulse.area (C:=C₀) (b:=b) (p:=p) J,∑ t:Children,∑ a:Bids,
    z (o,t,a) • cell s v o h t a
  map_add' x y:=by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib,smul_add]
  map_smul' c z:=by
    simp only [Pi.smul_apply,smul_assoc,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl;intro o _
    apply Finset.sum_congr rfl;intro t _
    apply Finset.sum_congr rfl;intro a _
    rw [smul_comm c (premiums C₀ s m b r)]

def measured (v:(i:I)→Palette C₀ (s i))(J:ℕ)(r:ℝ)(m:ℕ) :
    (Index R s h p→ℂ)→ₗ[ℂ]C(Upper,ℂ) := WilsonMacroscopicRichFourierFiledScalar.diagonal.comp (upper R s h v J r m)

theorem field (v:(i:I)→Palette C₀ (s i))(J:ℕ)(r:ℝ)(m:ℕ)(g:Body)(Ψ:Wave I) :
    measured R s h v J r m (weights R s h J r g Ψ)=gauge (restricted R (per:=p) s v h J Ψ r g m):=by
  change WilsonSeparatedOriginalSlabFourierCredit.gauge ((premiums C₀ s m b r) • _) = WilsonSeparatedOriginalSlabFourierCredit.gauge ((premiums C₀ s m b r) • _)
  congr 2
  apply Finset.sum_congr rfl;intro o ho
  rw [deposited]
  apply Finset.sum_congr rfl;intro t _
  apply Finset.sum_congr rfl;intro a _
  rw [weights,if_pos ho]

theorem allWeights (J:ℕ){r cap:ℝ}(Ψ:Wave I){F:C(UnitAddTorus Axes,ℂ)}
    (paid:WilsonSeparatedOriginalSlabFourierWeights.Received C₀ b J s r cap Ψ F)(g:Body):
    HasSum (fun k:K=>mFourierCoeff F k • weights R (p:=p) s h J r g
      (packet (wire (edge C₀ b J r cap) (r/(C₀).S.a b) k) (r/(C₀).S.a b)))
      (weights R s h J r g Ψ):=by
  apply Pi.hasSum.mpr;rintro ⟨o,t,a⟩
  by_cases ho:o∈Pulse.area (C:=C₀) (b:=b) (p:=p) J
  · simpa only [weights,if_pos ho,Pi.smul_apply,smul_eq_mul] using paid N p h o ho t a g
  · simp only [weights,if_neg ho,Pi.smul_apply,smul_eq_mul,mul_zero,hasSum_zero]
end YM.Integration.WilsonMacroscopicRichFourierCellBank
