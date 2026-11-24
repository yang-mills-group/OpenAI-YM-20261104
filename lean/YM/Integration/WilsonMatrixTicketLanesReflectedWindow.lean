import YM.Integration.WilsonMatrixTicketLanesReflectedWires
import YM.Integration.WilsonMatrixTicketLanesReflectedSites
import YM.FVA2.SectorMirror

/-! Finite-torus connected angular coefficients with the actual FVA2 reversed-bond images. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReflectedWindow
open Function Filter Finset Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet
open RGComparison.Core16.Forge RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open RGComparison.Core16.Spool RGComparison.Core16.Silk Contacts.Lyre Contacts.Lyre.Align
open WilsonMatrixTicketLanesReportedPrepaid WilsonMatrixTicketLanesReportedWords
open scoped Topology Classical
variable {G : Gauge} {c f : Side} (S : StepData c f)

def reflected (z : Rail G (Forestry S).Free) : Rail G (Forestry S).Free := z.map fun i=>(Align.via S i.1,i.2)

def inside (a : Site f) (r : ℕ) (z : Rail G (Forestry S).Free) :=
  ∀ j∈z,pdist (Hut.pad (Forestry S) j.1-a)≤r

/-- A word in actual free tangent coordinates transforms with the full orientation sign. -/
def value (z : Rail G (Forestry S).Free) (v : (Forestry S).Free→G.Color) := (z.map fun i=>v i.1 i.2).prod

theorem orientation (v : (Forestry S).Free→G.Color) (z : Rail G (Forestry S).Free) :
    value S z (FVA2.Both.atRef G S v) = (-1:ℝ)^z.length *value S (reflected S z) v := by
  induction z with
  | nil => simp [value,reflected]
  | cons i z ih =>
    change (FVA2.Both.atRef G S v i.1 i.2) * value S z (FVA2.Both.atRef G S v) =
      (-1:ℝ)^(z.length+1)*(v (Align.via S i.1) i.2 * value S (reflected S z) v)
    rw [FVA2.Both.sub_ref,ih,pow_succ]; change (-v (Align.via S i.1) i.2)*_= _; ring

variable (R : Run G) (b : ℕ)
local notation "Op" => R.family.path.levels.clock.op b 0
local notation "stepAt" p => R.family.path.levels.clock.op b p
local notation "T" p => Forestry (stepAt p)

/-- A single legal coarse translation for the whole window. The constant, shade and chamber
are fixed before all periodic volumes, true bounded pins, word pairs and their finite sites. -/
def Report : Prop := ∃ (P : Oven (Op).patch) (X : P.Form G), P.Offers X (Op).kernel ∧
  ∀ (r l d : ℕ),∃ C : ℝ,0≤C ∧ ∀ (p : ℕ) (a : Site (R.family.side (b+1) p)),∃ q : Site (R.family.side b p),
  ∀ (u : Directions G (R.family.side b p)),(∀i,‖u i‖≤X.Q)→∀ (w z : Rail G (T p).Free),w.length≤l→z.length≤d→
  ∀ h, 8*(h+h+1)≤(R.family.side (b+1) p).val→let center:=a+(stepAt p).ratio.embed q
    inside (stepAt p) center h w→inside (stepAt p) center h z→
    let A:=Spool.lens (S:=stepAt p) u X (T p)
    let mirror:=reflected (stepAt p) z
    train (fun g=>A.expect g (sing (mirror++w) g)-A.expect g (sing mirror g)*A.expect g (sing w g)) (Silk.gap A w mirror) ∧
      ∀ j≤r,|nth j (Silk.gap A w mirror)|≤C / Real.exp (shade X * (((R.family.side (b+1) p).val/8:ℕ):ℝ))

theorem original (paid : Paid G R.kit) : ∀ᶠ b : ℕ in atTop,Report R b := by
  filter_upwards [WilsonMatrixTicketLanesReflectedWires.original R paid] with b booked
  obtain ⟨P,X,offer,allFees⟩:=booked
  refine ⟨P,X,offer,?_⟩; intro r l d
  obtain ⟨C,hC,fee⟩:=allFees r l d
  refine ⟨C,hC,?_⟩;intro p a
  obtain ⟨q,region⟩:=WilsonMatrixTicketLanesReflectedSites.window (R.family.path.levels.clock.op b p).ratio (R.family.S.side_four b p) a
  refine ⟨q,?_⟩;intro u pin w z hw hz h clearance center hw' hz' A mirror
  have length : mirror.length=z.length := List.length_map ..
  obtain ⟨measured,decay⟩:=fee p (Forestry (R.family.path.levels.clock.op b p)) u pin w mirror hw (length.trans_le hz)
  refine ⟨measured,?_⟩;intro j hj
  apply decay j hj _;intro i hi k hk
  obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hk
  let first:=Hut.pad (Forestry (R.family.path.levels.clock.op b p)) i.1-center
  let second:=Hut.pad (Forestry (R.family.path.levels.clock.op b p)) v.1-center
  have h₁ : pdist first≤h := hw' _ hi
  have h₂ : pdist second≤h := hz' _ hv
  have legal : 8*(pdist first+pdist second+1)≤(R.family.side (b+1) p).val := by omega
  have sep:=region first second v.1.val.2 legal
  change (R.family.side (b+1) p).val≤8*Lattice.separation (center+first)
    (PertExtension.Orb.reflect (center+second,v.1.val.2)).1 at sep
  have eqI : center+first=Hut.pad (Forestry (R.family.path.levels.clock.op b p)) i.1 := by dsimp [first]; abel
  have eqV : center+second=Hut.pad (Forestry (R.family.path.levels.clock.op b p)) v.1 := by dsimp [second]; abel
  rw [eqI,eqV] at sep
  change (R.family.side (b+1) p).val/8≤Lattice.separation (Hut.pad (Forestry (R.family.path.levels.clock.op b p)) i.1) (PertExtension.Orb.reflect v.1.val).1
  change (R.family.side (b+1) p).val≤8*Lattice.separation (Hut.pad (Forestry (R.family.path.levels.clock.op b p)) i.1) (PertExtension.Orb.reflect v.1.val).1 at sep
  omega

end YM.Integration.WilsonMatrixTicketLanesReflectedWindow
