import YM.Integration.WilsonOriginalNullOriginGrid
import YM.Integration.WilsonOriginalNullRelocation
import YM.Integration.WilsonOriginalMicroscopicGuardedTrial

/-! Translation of the entire physical field across an embedded upper grid.
Independent sites may translate the three entering fields separately. Their
joint value is then sent through one original Wilson operator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedGrid
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels
open Extra.Histories Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open RG05Readout.Records WilsonOriginalNullCorridor MergeProof Next.Foundations Push.Local
open WilsonPositionProgramOriginalBlockedTrial WilsonOriginalMicroscopicGuardedTrial
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family

theorem numerator_at (d N p K:ℕ)(live:K ≤ N)(y:Site ((C₀).side K p))(x:(C₀).label d):
    numerator R d N p K y x=numerator R d N p K 0 x ∘ Lattice.translate y:=by
  let Q:=primary (0:Site ((C₀).side K p)) x
  have paid:=WilsonOriginalNullRelocation.registered (C₀) R.makes d N p K live 0 y Q
  let move:=Tour.placard (C₀) R.makes N p live y
  have mark:=WilsonOriginalNullRelocation.center ((C₀).labels.level d) 0 y move x
  dsimp only at paid
  change (Drift.stamp y move Q).density (0+y) ((C₀).localSection d) ((C₀).path.rep N p K)=_ at paid
  rw [show Drift.stamp y move Q=primary (0+y) x from mark,zero_add] at paid
  exact paid

theorem one (d N p K:ℕ)(live:K ≤ N)(y:Site ((C₀).side K p))(x:(C₀).label d)
    (U:Config G ((C₀).side K p)):
    let W:=(C₀).path.rep N p K
    part ((C₀).localSection d) y W U x=part ((C₀).localSection d) 0 W (Lattice.translate y U) x:=by
  intro W
  have same:=congrFun (numerator_at R d N p K live y x) U
  simp only [Function.comp_apply,original_field] at same
  have shifted:=vac_pull (C₀).path N p K R.makes.wilson live 1 y U
  rw [Lattice.pull_one] at shifted
  change ((W.eval U:ℂ)*_)=((W.eval (Lattice.translate y U):ℂ)*_) at same
  have quiet:(W.eval (Lattice.translate y U):ℂ)=W.eval U:=shifted
  rw [quiet] at same
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Tour.bright (C₀).path R.makes.wilson N p K live U).ne') same

theorem translated_flow (d N p f:ℕ)(y:Site ((C₀).side f p))(n:ℕ):
    ∀field:Config G ((C₀).side (f+n) p)→ℂ,Integrable field (prior G _)→
      let v:=(C₀).S.toDepth (show f ≤ f+n by omega) p
      flow (C₀) d N p f n (field ∘ Lattice.translate (v.embed y))=
        flow (C₀) d N p f n field ∘ Lattice.translate y:=by
  induction n with
  | zero=>
    intro field _ v
    simp only [flow,v,like_embed]
  | succ n ih=>
    intro field h v
    let w:=(C₀).S.toDepth (show f ≤ f+n by omega) p
    let r:=((C₀).path.levels.clock.op (f+n) p).ratio
    have emb:v.embed y=r.embed (w.embed y):=Next.Rank.Station.embed_comp w r v y
    change flow (C₀) d N p f n (transition (C:=C₀) d N p (f+n) (field ∘ Lattice.translate (v.embed y)))=_
    rw [emb,WilsonOriginalNullMovedOperator.commute (C₀) d N p (f+n) (w.embed y) field h]
    exact ih _ (WilsonOriginalNullCorridor.integrable (C₀) d N p h)

theorem carried_on (d N p f n:ℕ)(live:f+n ≤ N)(y:Site ((C₀).side f p))(x:(C₀).label d):
    let v:=(C₀).S.toDepth (show f ≤ f+n by omega) p
    carried R d live (v.embed y) x = carried R d live 0 x ∘ Lattice.translate y:=by
  intro v
  change flow (C₀) d N p f n (numerator R d N p (f+n) (v.embed y) x)=_
  rw [numerator_at R d N p (f+n) live (v.embed y) x]
  exact translated_flow R d N p f y n _ (tested R d live 0 x)

theorem all_faces (d:Fin 3→ℕ)(N p K:ℕ)(cut:K ≤ N)(o:Fin 3→Site ((C₀).side K p))
    (v:∀a:Fin 3,(C₀).label (d a))(s:Finset (Fin 3)) {u:ℕ}(earlier:u ≤ K)
    (U:Config G ((C₀).side u p)):
    actualTransport (C₀) (N:=N) (face (guarded R d N p K o v) s) earlier U=
    actualTransport (C₀) (N:=N) (fun W=>∏a∈s,
      part ((C₀).localSection (d a)) 0 ((C₀).path.rep N p K) (Lattice.translate (o a) W) (v a)) earlier U:=by
  apply congrArg (fun z=>actualTransport (C₀) (N:=N) z earlier U)
  funext W
  apply Finset.prod_congr rfl
  intro a _
  exact one R (d a) N p K cut (o a) (v a) W

end YM.Integration.WilsonOriginalMicroscopicGuardedGrid
end
