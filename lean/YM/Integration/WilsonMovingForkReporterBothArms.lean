import YM.Integration.WilsonMovingForkReporterCommitted
import YM.Integration.WilsonMovingForkReporterBraided

/-! The two measured radii in each comparable physical experiment share the same continuum frame and original table incomes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterBothArms
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonMovingForkReporterFilament WilsonMovingForkReporterBraided
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {l:Ultrafilter (ℕ×ℕ)}
  {H:(Bel C.book).Hierarchy} {z:Arch C} (F:Final C f S) (J₀:ℝ→tower S)
  {D E:ℕ→ℕ} {V:∀i,Vane C (D i)} {W:∀i,Vane C (E i)}

def Filed (J:Scaling S) (T:∀i,Vane C i) (d i:ℕ) (A B:ℝ):Prop :=
  ∀u:(Bel C.book).Field d, let field:=J₀ ((T i).wheel.r) d u
    ‖(J.U i d).symm field‖ ≤ A*‖u‖ ∧ ∃ y:Arm C S (l:Filter _) d field,
      (∀p,y.source p=heightV T i d p ((J.U i d).symm field)) ∧
        ∀ᶠ p:ℕ×ℕ in f.fuse,Cards.PaidAt C.S p.1 p.2 (purchaseWidth (T i))
         (C.beta p.1 p.2) (B*‖u‖) (C.O p.1 p.2 (y.source p) 0)

theorem original (lead:Leading F J₀) (made:C.Makes) (simple:G.Simple) (bliss:Bliss F l z H)
    (higher:Tendsto D atTop atTop) (lower:Tendsto E atTop atTop)
    (vanish₁:Tendsto (fun i=>(V i).wheel.r) atTop (𝓝 0))
    (vanish₂:Tendsto (fun i=>(W i).wheel.r) atTop (𝓝 0))
    (apart:∀ᶠ i in atTop,(W i).wheel.r < (V i).wheel.r)
    (stages₁:Tendsto (fun i=>(V i).k) atTop atTop) (stages₂:Tendsto (fun i=>(W i).k) atTop atTop)
    (paid₁:∀i,(V i).checked f H (D i)) (paid₂:∀i,(W i).checked f H (E i)):
    ∃ c:Pair V W,∃ J:Scaling S,Scribe f J c.report z F.sector l F.room.kernel H ∧
      (∀i,J.r (2*i)=(V (c.pick i)).wheel.r ∧ J.r (2*i+1)=(W (c.pick i)).wheel.r) ∧
      ∀d,∃ A B:ℝ,1≤A ∧ 0≤B ∧ ∀ᶠ i in atTop,
        Filed (f:=f) (l:=l) J₀ J c.report d (2*i) A B ∧ Filed (f:=f) (l:=l) J₀ J c.report d (2*i+1) A B := by
  obtain ⟨c⟩:=WilsonMovingForkReporterBraided.select higher lower vanish₁ apart
  obtain ⟨X,agrees⟩:=opens c vanish₁ vanish₂
  let arch:Course c.report := ⟨id,strictMono_id,fun _=>le_rfl,X,agrees⟩
  have same:arch.filed=c.report:=by funext i;rfl
  obtain ⟨J,dates,school,_,prices⟩:=WilsonMovingForkReporterCommitted.original F c.report J₀ lead arch
    made simple bliss (calendar c stages₁ stages₂) (earned c paid₁ paid₂)
  rw [same] at school prices
  refine ⟨c,J,school,?_,fun d=>?_⟩
  · intro i
    rw [dates]
    change X.r (2*i)=_ ∧ X.r (2*i+1)=_
    rw [agrees,agrees,even,odd]
    exact ⟨rfl,rfl⟩
  · obtain ⟨A,B,one,pos,income⟩:=prices d
    refine ⟨A,B,one,pos,?_⟩
    obtain ⟨start,qualifies⟩:=eventually_atTop.mp income
    have sale (j:ℕ)(hj:start≤j):Filed (f:=f) (l:=l) J₀ J c.report d j A B := by
      have got:=qualifies j hj
      change ∀u:(Bel C.book).Field d, _ at got
      unfold Filed
      rw [←agrees j]
      exact got
    filter_upwards [eventually_ge_atTop start] with i now
    exact ⟨sale _ (by omega),sale _ (by omega)⟩

end YM.Integration.WilsonMovingForkReporterBothArms
end
