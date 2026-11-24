import YM.Integration.WilsonViewerPrescribedPacket
import YM.Integration.WilsonPositionSeparatedProfileMatching
import YM.Integration.WilsonMSDictionaryVector

/-! The original signed separated profile and the independently elected finite
OPE experiment determine all fixed separated exterior readings of the same
public fields after the original continuum limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonViewerSignedDictionary
open Function Filter Set Finset MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Log Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score
open MS MS.Land MS.Fleet WilsonMSDictionaryVector WilsonPositionHomogeneousFrame
open WilsonPositionSeparatedProfileMatching
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  (simple:G.Simple)(lead:Leading F J){Y:(Bel R.family.book).Hierarchy}
  (paid:∀ d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
local notation "P" => homogeneous F J Z
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
variable {n:ℕ}

include lead paid simple Q in
theorem correlations (X:Scaling S)(foundation:Foundation F Q)
    (ν:ℝ)(d:ℕ)(φ:Test n)(v:Fin n→Sec G d)(order:ℕ)(g:ℝ→ℝ)(hg:Coupling G g)
    (clock:∃K:ℝ, 0<K ∧ ∀ᶠr in trail,g r≤K*|θ r|)
    (signed:∀ε:ℝ,0<ε→∀ᶠr in trail,
      ‖observed Z F J none d φ v r-polynomial Z M ν d φ v order (θ r)‖≤ε*|θ r|^order):
    matchesThrough Z M F J ν d φ v order:=by
  obtain ⟨K,Kp,clocks⟩:=clock
  intro ε ep
  let a:=ε/(2*K^order)
  have ap:0<a:=div_pos ep (mul_pos (by norm_num) (pow_pos Kp _))
  filter_upwards [phases Z F J Q lead paid simple X foundation d φ v g hg ap order,
    signed _ (half_pos ep),clocks,hg.positive] with r viewers bank same gp p
  have money:g r^order≤K^order*|θ r|^order:=by
    simpa only [mul_pow] using pow_le_pow_left₀ gp.le same order
  have row:‖observed Z F J p d φ v r-observed Z F J none d φ v r‖≤ε/2*|θ r|^order:=by
    refine (viewers p).trans ((mul_le_mul_of_nonneg_left money ap.le).trans_eq ?_)
    dsimp only [a]
    field_simp [Kp.ne']
  refine (norm_sub_le_norm_sub_add_norm_sub _ (observed Z F J none d φ v r) _).trans
    ((add_le_add row bank).trans_eq ?_)
  ring

include Q lead paid simple in
theorem ope {σ:Prescription (Press.portDeck G)}{branch:Bool}(matchMS:Main.Match Z simple M σ branch)
    (services:Services R.family f S)(ν:ℝ)(d:Fin n→ℕ)(h q:ℕ)(v:(j:Fin n)→RG17.Free R.family (d j))
    {E:Type}[Fintype E]{e:E→ℕ}(w:Labels S e){δ:ℝ}(dp:0<δ)
    (g:ℝ→ℝ)(K:Set (Points n))(error:ℝ→Test n→ℝ)
    (signed:∀ᶠr in trail,∀ψ:Test n,tsupport ψ⊆K →
      ∃ᶠs:ℝ in atTop,
       ‖(P r h).symm (RG17.basket Q h (d:=d) (fun j=>P r (d j) (v j)) r ψ)-
         experiment R.family d h Z M ν v ψ ((matchMS.separatedOPE ν).wilson.light h).choose q (g r) s‖≤error r ψ):
    ∃D:ℝ, 0≤D ∧ ∀ᶠr in trail,∀ψ:Test n,tsupport ψ⊆K →
      ∀(o:E4)(y:E→E4),ClearOf o y δ→∀p:Viewers F,
      ‖upon (spectator F p) h o y w (RG17.basket Q h (d:=d) (fun j=>P r (d j) (v j)) r ψ)-
        upon (spectator F p) h o y w (P r h (prediction R.family d h Z M ν v ψ q (g r)))‖ ≤D*error r ψ:=by
  let panel:=((matchMS.separatedOPE ν).wilson.light h).choose
  have ready:Read.Detected (Measure.outlook Z.scheme Z.criterion) panel:=
    ((matchMS.separatedOPE ν).wilson.light h).choose_spec.2
  obtain ⟨D,Dn,all⟩:=WilsonViewerPrescribedPacket.discrepancy F Q J Z simple lead paid w dp services h
  refine ⟨D,Dn,?_⟩
  filter_upwards [signed,all] with r bank cost ψ support o y clear p
  let physical:=RG17.basket Q h (d:=d) (fun j=>P r (d j) (v j)) r ψ
  have limit:=experiment_limit R.family d h Z M ν v ψ matchMS panel ready q (g r)
  have amount:‖(P r h).symm physical-prediction R.family d h Z M ν v ψ q (g r)‖≤error r ψ:=
    le_of_tendsto_of_frequently ((tendsto_const_nhds (x:=(P r h).symm physical)).sub limit).norm (bank ψ support)
  exact (cost o y clear p physical _).trans (mul_le_mul_of_nonneg_left amount Dn)

end YM.Integration.WilsonViewerSignedDictionary
end
