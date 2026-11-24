import YM.Integration.WilsonReflectedTrialEngineering
/-! On the common embedded reporting grid, the same signed dossier is
the difference of the two physically normalized conditional singletons.
Their raw and trial mesh factors are retained separately. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedTwoGridFields
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonReflectedTrialEngineering
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p f:ℕ}
local notation "C₀" => R.family
local notation "space" i:max => Config G ((C₀).side i p)
local notation "P₀" i:max => (C₀).path.rep N p i

theorem scaled {K:ℕ}(fK:f ≤ K)(F:space K→ℂ)(paid:Integrable F (prior G _))(z:ℂ):
    gust (C₀).path N p K (z • F) f fK=z • gust (C₀).path N p K F f fK:=by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le fK
  exact gust_scalar R f n F paid z

theorem raw (d:ℕ)(cut:f ≤ N)(ready:(C₀).ref d ≤ f)(o:Site ((C₀).side f p))(x:(C₀).label d)(U:space f):
    let P:=((C₀).factory d N p)
    let I:space N→ℂ:=(C₀).O N p x (((C₀).S.toDepth cut p).embed o)
    calValues (C:=C₀) d N p f (P.terminal.symm x) (Lattice.translate o U)=
      ((C₀).S.a f:ℂ)^d*((P₀ f).eval U:ℂ)*actualTransport (C₀) (N:=N) I cut U:=by
  intro P I
  let α:ℂ:=((C₀).S.a f:ℂ)^d
  let E:space N→ℂ:=fun V=>(P₀ N).eval V • I V
  have si:Envelope I:=Envelope.compactC ((C₀).continuousO ..)
  have pay:Integrable E (prior G _):=ActualWilsonAbsoluteTransport.weighted (C₀) R.makes (le_refl N) si
  have read:=congrFun (WilsonOriginalNullOriginGrid.public_grid R d N p cut ready o (P.terminal.symm x)) U
  have atCut:P.terminal (P.terminal.symm x)=x:=P.terminal.apply_symm_apply x
  change dyes (C₀) f N p cut (α • (C₀).O N p (P.terminal (P.terminal.symm x)) _ ) U=_ at read
  rw [atCut] at read
  have agree:(fun V:space N=>((P₀ N).eval V:ℂ)*(α*I V))=α • E:=by
    funext V;simp only [Pi.smul_apply,smul_eq_mul,E,Complex.real_smul];ring
  change gust (C₀).path N p N (fun V:space N=>((P₀ N).eval V:ℂ)*(α*I V)) f cut U=_ at read
  rw [agree,scaled R cut E pay α] at read
  simp only [Function.comp_apply] at read
  rw [←read]
  change α*gust (C₀).path N p N E f cut U=α*((P₀ f).eval U:ℂ)*_
  rw [←actualTransport_unnormalize (C₀) R.makes (le_refl N) I cut U,Complex.real_smul]
  ring

theorem restarted (d n:ℕ)(high:f+n ≤ N)(o:Site ((C₀).side f p))(x:(C₀).label d)(U:space f):
    let K:=f+n
    let embed:=(C₀).S.toDepth (Nat.le_add_right f n) p
    let F:=fun V:space K=>part ((C₀).localSection d) (embed.embed o) (P₀ K) V x
    track R d N p K (numerator R d N p K 0 x) f (Lattice.translate o U)=
      (((C₀).S.steps f n).val:ℂ)^d*((P₀ f).eval U:ℂ)*actualTransport (C₀) (N:=N) F (Nat.le_add_right f n) U:=by
  intro K embed F
  let G₀:=numerator R d N p K 0 x
  let E:=numerator R d N p K (embed.embed o) x
  have enter:=congrFun (segment R d N p G₀ n (le_refl K)) (Lattice.translate o U)
  rw [at_top] at enter
  have same:=congrFun (WilsonOriginalMicroscopicGuardedGrid.carried_on R d N p f n high o x) U
  change flow (C₀) d N p f n E U=flow (C₀) d N p f n G₀ (Lattice.translate o U) at same
  rw [enter,←same,weight R d f n E (tested R d high _ x),WilsonReceivedQUnitPosterior.raw]
  have val:E=fun V:space K=>(P₀ K).eval V • F V:=by
    funext V;rw [Complex.real_smul];exact original_field R d N p K _ x V
  rw [val]
  change _*gust (C₀).path N p K _ f _ U=_*((P₀ f).eval U:ℂ)*_
  rw [←actualTransport_unnormalize (C₀) R.makes high F (Nat.le_add_right f n) U,Complex.real_smul]
  ring

end YM.Integration.WilsonReflectedTwoGridFields
end
