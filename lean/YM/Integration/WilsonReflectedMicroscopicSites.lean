import YM.Integration.WilsonThermometerWeakStately
import YM.Integration.WilsonReflectedArmsCapture
import YM.RG16.Unmasked.Purchased

/-! True finest-grid children in the reflected cells and their own ancestors.
Each enrolled child supplies one scalar, regular and forced trajectory. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReflectedMicroscopicSites
open Function Filter MeasureTheory Lattice Wilson RG Source Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetJoint
open WilsonThermometerReflectedTrajectory
open scoped Classical BigOperators Topology
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) {N p J:ℕ} {I:Type}
local notation "C" => R.family
local notation "V" => Site (R.family.side J p)
local notation "P" => hands C p J
local notation "E" => Mix.camp C p J
variable (z : I → Site (R.family.side N p))
def tip (u:V×I) : Site (R.family.side N p) := WilsonThermometerReflectedRoster.endpoint (k:=J) (N:=N) (p:=p) R (z u.2) (P u.1) u.1
def site (j:ℕ) (u:V×I) : Site (R.family.side j p) := WilsonThermometerOwnOffsetNectar.location (N:=N) (p:=p) R (tip R z u) j

theorem base (valid:J≤N) (j:ℕ) (i:I) : site R z j ((0:V),i)=WilsonThermometerOwnOffsetNectar.location (N:=N) (p:=p) R (z i) j :=by
  change WilsonThermometerOwnOffsetNectar.location (N:=N) (p:=p) R (affine ((P 0).1) (E N 0) (z i)) j=_
  rw [P_on,zeroMama C J p N valid]
  simp [affine]

theorem transformed {j:ℕ} (jl:J≤j) (ln:j≤N) (u:V×I) :
    site R z j u=affine (P u.1).1 (E j u.1) (WilsonThermometerOwnOffsetNectar.location (N:=N) (p:=p) R (z u.2) j) :=
  WilsonThermometerReflectedRoster.parent R (z u.2) (P u.1) u.1 jl ln

theorem collar {j:ℕ} (jl:J≤j) (ln:j≤N) : Collar (site R z j) (0:V) (E j) P := by
  intro v _ i
  rw [base R z (jl.trans ln)]
  exact transformed R z jl ln (v,i)

theorem adjacent {j:ℕ} (hn:j<N) :
    (R.family.path.levels.clock.op j p).ratio.parent ∘ site R z (j+1) = site R (J:=J) z j :=by
  funext u
  exact WilsonThermometerOwnOffsetGeometry.parent R (tip R z) hn u

theorem anchor {i:ℕ} (ji : J ≤ i) (inN:i≤N) (i₀ : I) (h:WilsonThermometerOwnOffsetNectar.location (N:=N) (p:=p) R (z i₀) i=0) (c:V) :
    site R z i (c,i₀)=E i c :=by rw [transformed R z ji inN,h];simp [affine]

variable [Fintype I] [DecidableEq I]
theorem joint (simple:G.Simple) (k t:ℕ)
    (separated:∀a b:V×I,a≠b→(R.family.path.levels.budget k).B^2<separation (site R z k a) (site R z k b)) :
    Matchup R.family.path (mutt R.alloy.B.a R.Q) (renal R.alloy.B.a) p N k (site R z)
      (fun j (_:V×I)=>radius R t k j) (Names V I) :=
  WilsonThermometerOwnOffsetGeometry.admitted R simple (tip R z) t (Names V I) separated

/-- The base copy sees exactly its original cutoff configuration. The same
finite width t works for all admitted periods, cutoffs and collider positions. -/
theorem entered (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (D:ℕ) :
    ∃t≥D+3,∀ᶠ k in atTop,∀ p N (kn:k≤N) (J:ℕ) (valid:J≤N)
      (d:I→ℕ) (_:∀i,d i≤D) (z:I→Site (R.family.side N p)) (V':(i:I)→Sight C (d i) p)
      (r:(i:I)→Emblems C (d i))
      (_:∀i,WilsonThermometerOffsetTrajectory.Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (d i)
           (WilsonThermometerOffsetResidue.digits R N p (z i)) (V' i) (r i))
      (y:(i:I)→Palette C (d i)), (∀i,size (y i)≤1) →
      ∀i:I,∃(g:∀j,Config G (R.family.side j p)→ℂ) (K:∀j,ℕ → Config G (R.family.side j p)→ℂ),
        Stately R.family.path (far R.alloy.B.a) k N p (fun j=>site R z j ((0:Site (R.family.side J p)),i))
          (radius R t k) g K
          ((center R.family.S p valid 0).copy 0 (WilsonThermometerIntrinsicRoster.source R d z y r kn i)) R.doors :=by
  obtain ⟨t,lb,bought⟩:=WilsonThermometerWeakStately.original R simple shop D
  refine ⟨t,lb,bought.mono ?_⟩
  intro k here p N kn J valid d cap z V' r legal y small i
  have chosen:=here p N kn I d cap z V' r legal (fun _=>(1,false)) (fun _=>0) y small i
  have a : WilsonThermometerReflectedRoster.endpoint R (z i) (1,false) (0:Site (R.family.side k p))=z i := by
    change affine 1 (Mix.camp C p k N 0) (z i)=_
    rw [zeroMama C k p N kn];simp [affine]
  have paid : WilsonThermometerReflectedRoster.source R d z (fun _=>(1,false)) (fun _=>0) y r kn i =
      WilsonThermometerIntrinsicRoster.source R d z y r kn i :=by
    change stepUp (1,false) (Mix.camp C p k N 0) _=_
    rw [zeroMama C k p N kn,stepid]
  change Stately _ _ _ _ _ (fun j=>WilsonThermometerOwnOffsetNectar.location (N:=N) (p:=p) R (WilsonThermometerReflectedRoster.endpoint R (z i) (1,false) (0:Site (R.family.side k p))) j) _ _ _
    (WilsonThermometerReflectedRoster.source R d z (fun _=>(1,false)) (fun _=>0) y r kn i) _ at chosen
  rw [a,paid] at chosen
  have copy_id (f : Config G (R.family.side N p) → ℂ) :
      (center R.family.S p valid 0).copy 0 f = f := funext ((center R.family.S p valid 0).copy_zero f)
  simp only [base R z valid,copy_id]
  exact ⟨_,_,chosen⟩
end YM.Integration.WilsonReflectedMicroscopicSites
