import YM.Integration.WilsonMaxwellThermometerReflectedEnteredPhysical
import YM.Integration.WilsonMaxwellThermometerReflectedLowerReturn
/-! On each fixed real physical chart the same issued b and two chiral
responses are resubmitted on the auxiliary inversion. The purchase for the
occupied tangent retains its actual signed incidence error. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedMeteredLowerReturn
open Function Filter Set Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Embroider Source Source.Drops
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open RG17 PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPositionCapTransport (Book)
open WilsonPositionThermometerCapStation (Group)
open WilsonPositionCorrectedCap (adjusted)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMaxwellThermometerReflectedPhysicalColumns (levels)
open WilsonMaxwellThermometerReflectedStation (Name source)
open WilsonMaxwellThermometerReflectedEntered (current)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{T:Table R.family.book}
variable (F:Final R.family f T)(P:ℝ→tower T)(V:Store G)
variable {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}(A:ℝ→Group R.family 6)
variable (a:Axis)(b:Sec G 6)(d:Fin 2→ℕ)(fit:∀i,levels i<d i)
variable {D k u e:ℕ}
local notation "Q" => deck (G:=G) levels d fit

open MeasureTheory XSpace.Cirrus XSpace.Rose XSpace.Structure1 XSpace.Photo XSpace.Tornado XSpace.Retirement Table.Pairing
open WilsonMaxwellThermometerLowerPointGram (occupied)
open WilsonMaxwellThermometerLowerGramPrice (token reassemble)
open WilsonMaxwellThermometerReflectedFirstPrice (filed)
open WilsonMaxwellThermometerReflectedIncidence (Gram Pair mass site)
open WilsonMaxwellThermometerFiniteTangent (credit)
open WilsonMaxwellThermometerCommonTangent (Equivariant)
open WilsonMaxwellThermometerOriginal (lower)
open WilsonMaxwellThermometerReflectedTangent (raised)

theorem original (x:E4)(hx:0<x a)(W:Initialize G){V₀:Normalize.Store G}(K:Pick V₀)
    (D₁ D₂:Module.End ℂ (Sec G 4))(h₁:Equivariant D₁)(h₂:Equivariant D₂)
    (simple:G.Simple)(book:Book (f:=f) (l:=l) (H:=H) A P)(lead:Leading F P)
    (paid:WilsonPositionProgramNominatedMenuInvoice.issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1 ≤ e)(cap:capP Q ≤ k):
    ∃β:Bulb (site x) a,∃φ:Wilt Q,∃floor:ℕ,
      WilsonPositionProgramReflectedRead.reading Q a φ=mass a x β ∧
      (∫w:Pair,WilsonPositionProgramReflectedRead.reading Q a φ w)=1 ∧
      ∀ᶠ r in trail,let Z:=adjusted F P V A r
      ∀(U:XSpace.Run){stage:ℕ}(B:WilsonPositionProgramReporterBand.Band R U stage)
      (q:ℕ)(charge δ:ℝ),0≤charge → 0<δ → ∀ᶠ t:ℕ in atTop,let m:=B.reporter+t
      let M:=U.step (B.index t)
      ∀N per:ℕ,Z.station.k<N → ∀v₀:ℕ,floor ≤ v₀ → B.lower t ≤ v₀ → v₀ ≤ m →
      ∀Nₐ:ℕ,m ≤ Nₐ → ∀c∈M.Box,
      let J:=current R d fit big φ (fun n=>source R d fit Z a b Z.station.k n N per) m v₀ Nₐ k
      let y:=J-filed a x W V₀ β b M c
      let G₀:=reassemble a x (Gram a x W V₀ β M c)
      let ground:=fun z:occupied G a x=>credit W K M (raised a x z) (D₁ (lower G)) (D₂ (lower G))
      (∀z:occupied G a x,‖y-G₀ z‖ ≤ charge*(1+(B.index t:ℝ))^q → ‖ground z‖<δ) ∧
      ∃z:occupied G a x,(∀z',‖y-G₀ z‖ ≤ ‖y-G₀ z'‖) ∧ ‖ground z‖<δ:=by
  obtain ⟨β,C,J,hC,hJ,first⟩:=WilsonMaxwellThermometerReflectedFirstPrice.original a x W V₀ hx b
  obtain ⟨E,hE,wfile⟩:=WilsonMaxwellThermometerReflectedFirstPrice.bounded a x W V₀ β b
  obtain ⟨φ,w,shape,read,int⟩:=WilsonPositionProgramReflectedRead.original Q a x β 1
  obtain ⟨floor,file⟩:=WilsonMaxwellThermometerReflectedEnteredPhysical.original F P V A a b d fit
    simple book lead paid big rails he cap
  obtain ⟨L,hL,ground⟩:=WilsonMaxwellThermometerReflectedTangent.ground a x W K simple D₁ D₂ h₁ h₂
  refine ⟨β,φ,floor,read,int,?_⟩
  filter_upwards [file] with rad gather
  intro Z U stage B q charge δ non pos
  obtain ⟨H₀,hH,p,fee⟩:=gather U B φ w shape
  let r:=p+q
  let T:=L*C*(H₀+J+(charge+H₀+E))
  have data:Tendsto (fun t:ℕ=>T*((U.step (B.index t)).spacing*(1+(B.index t:ℝ))^r)) atTop (𝓝 0):=by
    simpa only [Function.comp_apply,mul_zero] using ((WilsonMaxwellThermometerReflectedTangent.decay U r).comp B.cofinal).const_mul T
  have steps:Tendsto (fun t=>U.step (B.index t)) atTop Front:=
    (goesFront (Expense.Stretched.runs U)).comp B.cofinal
  filter_upwards [data.eventually (gt_mem_nhds pos),fee,steps.eventually wfile,steps.eventually first,
    steps.eventually ground] with t small paid pub obs out
  intro m M N per live v₀ base start vm Nₐ upper c hc cur y G₀ net
  let h:=1+(B.index t:ℝ)
  have h₁:1≤h:=by dsimp [h];linarith [Nat.cast_nonneg (α:=ℝ) (B.index t)]
  have hpow:1≤h^r:=one_le_pow₀ h₁
  have pprice:h^p≤h^r:=pow_le_pow_right₀ h₁ (Nat.le_add_right ..)
  have qprice:h^q≤h^r:=pow_le_pow_right₀ h₁ (Nat.le_add_left ..)
  have ph:0≤H₀*h^p:=mul_nonneg hH (pow_nonneg (zero_le_one.trans h₁) _)
  have cost:‖cur‖≤H₀*h^p:=
    (pi_norm_le_iff_of_nonneg ph).2 (paid N per live v₀ base start vm Nₐ upper)
  have charges (z:occupied G a x)(hw:‖y-G₀ z‖≤(charge+H₀+E)*h^r):‖net z‖<δ:=by
    have d:=obs c hc z (cur) ‖y-G₀ z‖ le_rfl
    have inv:‖token a x z‖≤C*((H₀+J+(charge+H₀+E))*h^r):=by
      apply d.trans
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [add_mul,add_mul]
      apply add_le_add _ hw
      exact add_le_add (cost.trans (mul_le_mul_of_nonneg_left pprice hH))
        (le_mul_of_one_le_right hJ hpow)
    have slip:=out z
    change ‖net z‖≤L*M.spacing*‖token a x z‖ at slip
    apply lt_of_le_of_lt (slip.trans (mul_le_mul_of_nonneg_left inv (mul_nonneg hL M.positive.le)))
    calc
      _ = T*(M.spacing*h^r):=by dsimp [T];ring
      _ < δ:=small
  constructor
  · intro z err
    apply charges z (err.trans _)
    exact mul_le_mul (by linarith only [hH,hE]) qprice
      (pow_nonneg (zero_le_one.trans h₁) _) (by linarith only [non,hH,hE])
  · obtain ⟨z,solves⟩:=WilsonMaxwellThermometerReflectedCalibration.solved a x (Gram a x W V₀ β M c) y
    refine ⟨z,solves,charges z ?_⟩
    have h:=solves 0
    change ‖y-G₀ z‖≤‖y-(WilsonMaxwellThermometerReflectedCalibration.detector a x (Gram a x W V₀ β M c)) 0‖ at h
    rw [map_zero,sub_zero] at h
    apply h.trans (((norm_sub_le ..).trans (add_le_add cost (pub c hc))).trans _)
    rw [add_mul,add_mul]
    linarith only [mul_le_mul_of_nonneg_left pprice hH,
      le_mul_of_one_le_right hE hpow,mul_nonneg non (zero_le_one.trans hpow)]
end YM.Integration.WilsonMaxwellThermometerReflectedMeteredLowerReturn
