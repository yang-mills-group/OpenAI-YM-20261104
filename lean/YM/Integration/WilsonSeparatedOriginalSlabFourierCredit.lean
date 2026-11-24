import YM.Integration.WilsonSeparatedOriginalSlabFourierMeter
import YM.Integration.WilsonMacroscopicRichChildRemainder

/-! The original unnormalized RG16 capture of the whole addressed field on every old configuration, using one bare density and the original physical kernels. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierCredit
open Function Set UnitAddTorus Lattice Wilson Source RG PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Address RG05Readout.Nuclear
open RG16.Literal WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierRoom WilsonSeparatedOriginalSlabPlaneTest WilsonSeparatedOriginalSlabFourierCharacters
open WilsonSeparatedOriginalSlabFourierLattice WilsonSeparatedOriginalSlabFourierAtlas WilsonSeparatedOriginalSlabFourierCylinder
open scoped Topology BigOperators Classical
local notation "I"=>Fin 3
local notation "K"=>Axes→ℤ
variable {G:Gauge}{A:Type*}[TopologicalSpace A]

def gauge (f:C(I → A,ℂ)):C(A,ℂ):=⟨fun U=>f (fun _=>U),f.continuous.comp (continuous_pi (fun _=>continuous_id))⟩

variable (R:Run G){N per b:ℕ}
local notation "Ufine"=>Config G (R.family.side N per)

def intake {j:ℕ}(h:j≤N)(d:ℕ)(W:Config G (R.family.side j per)):C(I → Ufine,ℂ)→ₗ[ℂ]ℂ where
  toFun f:=credit R.family N per d (gauge f) j h W
  map_add' f k:=by
    let E:Fin 2→Cut R.family N per:=![(gauge f:Ufine→ℂ),(gauge k:Ufine→ℂ)]
    have ce(i:Fin 2):Continuous (E i):=by fin_cases i;exact (gauge f).continuous;exact (gauge k).continuous
    have eq:=congrFun (IntrinsicProductLinearity.credit_sum R.family N per d j h (fun _:Fin 2=>(1:ℂ)) E ce) W
    change credit R.family N per d (gauge (f+k)) j h W = _
    have add:(gauge (f+k):Ufine→ℂ)=(gauge f:Ufine→ℂ)+(gauge k:Ufine→ℂ):=by funext U; rfl
    rw [add];simpa [E,Fin.sum_univ_two] using eq
  map_smul' c f:=by
    let E:Unit→Cut R.family N per:=fun _=>gauge f
    have eq:=congrFun (IntrinsicProductLinearity.credit_sum R.family N per d j h (fun _:Unit=>c) E (fun _=>(gauge f).continuous)) W
    change credit R.family N per d (gauge (c • f)) j h W = _
    have scale:(gauge (c • f):Ufine→ℂ)=c • (gauge f:Ufine→ℂ):=by funext U; rfl
    rw [scale];simpa [E,Pi.smul_apply] using eq

theorem original (b:ℕ)(s:I→ℕ){r cap:ℝ}(rp:0<r)(cp:0≤cap)(Ψ:Wave I)(seen:∀y∈tsupport Ψ.val,∀i,‖y i‖≤cap){B:ℝ}(bp:0≤B)(fund:Tall Ψ (rank s+1) 1 B):
    let J:=WilsonSeparatedOriginalSlabActiveWeights.range R.family b r cap
    let P:=edge R.family b J r cap
    ∃F:C(UnitAddTorus Axes,ℂ),Summable (fun k:K=>‖mFourierCoeff F k‖*height k^load s) ∧
      (∑'k:K,‖mFourierCoeff F k‖*height k^load s)≤bank P (rank s+1) B*WilsonSeparatedOriginalSlabFourierBudget.charge Axes (load s) ∧
      ∀(N per:ℕ)(h:b≤N)(v:(i:I)→Palette R.family (s i))(g:Body)(m d j:ℕ)(hj:j≤N)(W:Config G (R.family.side j per)),
        HasSum (fun k:K=>mFourierCoeff F k *credit R.family N per d (gauge (restricted R (per:=per) s v h J (packet (wire P (r/R.family.S.a b) k) (r/R.family.S.a b)) r g m)) j hj W)
          (credit R.family N per d (constellation (C:=R.family) s v r Ψ h m g) j hj W):=by
  intro J P
  obtain ⟨F,law,bill,paid⟩:=WilsonSeparatedOriginalSlabFourierMeter.original R s b J rp cp Ψ seen bp fund
  refine ⟨F,law,bill,?_⟩;intro N per h v g m d j hj W
  have eq:=paid N per h v g m (intake R hj d W)
  rw [selected R s v h rp Ψ seen g m] at eq
  have actual:(gauge (WilsonSeparatedOriginalReplicaExperiments.assembled R (per:=per) s v h Ψ r g m):Config G (R.family.side N per)→ℂ)=constellation (C:=R.family) s v r Ψ h m g:=funext (WilsonSeparatedOriginalReplicaExperiments.diagonal R s v h Ψ r g m)
  rw [←actual];exact eq

end YM.Integration.WilsonSeparatedOriginalSlabFourierCredit
