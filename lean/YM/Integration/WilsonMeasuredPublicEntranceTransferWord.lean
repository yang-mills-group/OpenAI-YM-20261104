import YM.Integration.WilsonMeasuredPublicEntranceTransferCones
import YM.Integration.WilsonAddressedFiniteGuardCapital

/-! The unrestricted K observable at the original N vacuum, including
its true scalar, tested coefficients, positions, and every occupied mark. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferWord
open Function Set Finset Lattice RG Wilson Cells
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonMeasuredPublicEntranceTransferCones (windows)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}(d:I→ℕ){K N p:ℕ}
local notation "C₀" => R.family
local notation "S₀" => (C₀).S
local notation "W" => Config G ((C₀).side K p)
local notation "H" j:max => (C₀).path.levels.clock.hatBeta j
variable (v : (i : I) → R.family.label (d i)) (o : I → Site (R.family.side K p)) (s : Finset I)

def field (U:W):ℂ:=∏i∈s,uncut R (d i) N p K (o i) (v i) U

def price:ℝ:=∏i∈s,WilsonAddressedFiniteGuardFields.cap R d N p K v i

theorem gross (U:W):‖field (N:=N) R d v o s U‖≤price (N:=N) (K:=K) (p:=p) R d v s:=by
  unfold field price;rw [norm_prod]
  apply prod_le_prod (fun _ _=>norm_nonneg _)
  intro i _
  exact ((WilsonAddressedFiniteGuardFields.unary R d N p K o v i).2.2 U).2

theorem cash (live:K≤N){B:ℝ}(bp:0≤B)(e:ℕ)(fund:∀i,((C₀).labels.level (d i)).coeffSize (v i)≤B*(H K)^e):
    2*price (N:=N) (K:=K) (p:=p) R d v s≤WilsonAddressedFiniteGuardCapital.price R d B s*(H K)^(WilsonAddressedFiniteGuardCapital.power R d e s):=
  WilsonAddressedFiniteGuardCapital.original R d live v bp e fund s

theorem localWord (r:ℕ)(cover:∀i∈s,stencilRadius (C₀) (d i)≤r){M:Set (Site ((C₀).side K p))}
    (fits:∀i∈s,window (o i) r⊆M):Interior M (field (N:=N) R d v o s):=by
  apply Interior.combines
  intro i used
  apply (WilsonOriginalPublicReflectedTrace.local_trial (N:=N) R (d i) (v i) (o i)).enlarges
  intro z hz
  apply fits i used
  exact sparrow.mpr ((sparrow.mp hz).trans (cover i used))

end YM.Integration.WilsonMeasuredPublicEntranceTransferWord
end
