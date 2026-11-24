import YM.Integration.WilsonPhysicalStationPureBorn

/-! Price of the actually observed graded Wilson pair after both physical regulators on its true two rulers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationPureReleased
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Further.CorrectedLift Next.Rank Next.Rank.Station
open WilsonPhysicalStationFullVote (Head)
open WilsonPhysicalStationPureReceipt (ballot coefficients signed left)
open WilsonPhysicalStationBasisOwners (Earned)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationObservedEntry (born)
open scoped Topology Classical BigOperators Matrix

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{H:(Bel R.family.book).Hierarchy}
    (F:Final R.family f S){ℓ:Ultrafilter (ℕ×ℕ)}(J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
    {m k h e:ℕ}(hm:h ≤ m)(hk:h ≤ k)(ca:(V m).checked f H m)(cb:(V k).checked f H k)(q:ℕ)(eh:e ≤ h)
set_option quotPrecheck false
local notation "C₀" => standard R.family
local notation "A₀" => V m
local notation "B₀" => V k
local notation "rails" => R.family.path.levels
variable (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(v:Head R.family h→R.family.label h)(g:ℝ)
    (owner:Earned R F (ℓ:=ℓ) J₀ J V hm hk ca cb eh w v g)

include owner in
theorem earlier (u:(C₀).Field h):
    J.U k h (ballot R J₀ J V (k:=k) q u)-left R J₀ J V (k:=k) q v u∈LinearMap.range (F.sector.derivatives.rise eh):=by
  unfold WilsonPhysicalStationPureReceipt.left
  rw [sub_sub_cancel,map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (owner.lower i).2

def ink (u z:(C₀).Field h)(ξ:Points 2)(p:ℕ×ℕ):ℂ:=
  signed R J₀ J V hm hk cb q w u ((J₀ (A₀).wheel.r h).symm (J.U m h z))
    (A₀).k (choose (rails) (A₀).b (A₀).k ξ) p

def bill (u z:(C₀).Field h)(ξ:Points 2)(p:ℕ×ℕ):ℂ:=
  (signal R p.1 p.2 (A₀).k (B₀).k h q (mag (rails) (A₀).b (A₀).k) (mag (rails) (B₀).b (B₀).k):ℂ)*
    ∑i:Head R.family h,coefficients R J₀ J V (k:=k) q u i*born R h (tested (rails) (A₀).b (A₀).k ξ) z i.val

include owner in
theorem original (below:(ℓ:Filter _) ≤ f.fuse)(u z:(C₀).Field h)(ξ:Points 2)
    (fit:FitSky (rails) (A₀).b (A₀).k ξ){ε:ℝ}
    (paid:∀ᶠp in (ℓ:Filter _),‖ink R J₀ J V hm hk cb q w u z ξ p-bill R J₀ J V (k:=k) (m:=m) q u z ξ p‖ ≤ ε):
    let x:=tested (rails) (A₀).b (A₀).k ξ
    ‖S.classMoment S (fun _:Fin 2=>h) ((A₀).wheel.r • x) ![left R J₀ J V (k:=k) q v u,J.U m h z]-
      ((((B₀).wheel.r/(A₀).wheel.r)^h*g^q:ℝ):ℂ)*(C₀).classMoment (C₀) (fun _:Fin 2=>h) x ![ballot R J₀ J V (k:=k) q u,z]‖ ≤ ε:=by
  intro x
  have actual:=WilsonPhysicalStationPureReceipt.original R J₀ J V hm hk cb q w v below owner.physical
    u ((J₀ (A₀).wheel.r h).symm (J.U m h z)) (A₀).k (choose (rails) (A₀).b (A₀).k ξ)
    (WilsonPhysicalStationObservedGrid.separated R (A₀) ξ fit)
  rw [WilsonPhysicalStationObservedGrid.actual] at actual
  simp only [LinearEquiv.apply_symm_apply] at actual
  have heat:=WilsonPhysicalStationPureBorn.thermal R V (m:=m) (k:=k) (h:=h) q owner.kinetic
  have converted:=Complex.continuous_ofReal.continuousAt.tendsto.comp heat
  have independent:Tendsto (bill R J₀ J V (k:=k) (m:=m) q u z ξ) (ℓ:Filter _)
      (𝓝 (((((B₀).wheel.r/(A₀).wheel.r)^h*g^q:ℝ):ℂ)*(C₀).classMoment (C₀) (fun _:Fin 2=>h) x
        ![ballot R J₀ J V (k:=k) q u,z])):=by
    unfold bill
    rw [WilsonPhysicalStationPureBorn.matrix]
    exact converted.mul tendsto_const_nhds
  exact le_of_tendsto (actual.sub independent).norm paid

end YM.Integration.WilsonPhysicalStationPureReleased
end
