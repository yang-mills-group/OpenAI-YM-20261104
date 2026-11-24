import YM.Integration.WilsonThermometerWeakGroupFiling

/-! The filed physical group word reads a genuine free field, including its unit,
under the selected tagged covariance. Rescaling that field by the physical
threshold/coupling ratio gives the compensated weak coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakGroupCoordinate
open Function Filter RG RG12 Extra.Histories Lattice Wilson
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Source Labels
open Next.Rank.Configuration Normal Rise Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "Lev" => R.family.path.levels
local notation "Corr" => WilsonThermometerWeakWickRoom.corrected R

def contracted {k b p:ℕ} (d:ℕ) (wide:4*b≤wood (Lev) k)
    (E:AtlasData G (C).S p) (W:poly (slotC G b)) :=
  trim (exchange (faceTest C d k) (milk (control (k:=k) E 0 (wood (Lev) k))
    (rename (calls wide) W))) (key G d) d

theorem original {k N p d D:ℕ} (hk:k≤N)
    (live:2*(sizeQ C k+1)<((C).side k p).val) (wide:4*sizeQ C k≤wood (Lev) k)
    (E:AtlasData G (C).S p) (good:Hail C k p D E)
    (q:poly (Up C k p (sizeQ C k))) :
    let t:=((C).path.rep N p k).p.threshold
    let g:=GaugeScale C k N p
    let W:=sender live t g q
    let F:=(C).labels.level d
    Spirit W → ∃ y:F.Coeff,expose F y=contracted R d wide E W ∧
      expose F (F.scaled (t/g) y)=Corr live wide (control (k:=k) E 0 (wood (Lev) k)) q N d := by
  intro t g W F spin
  let K:=control (k:=k) E 0 (wood (Lev) k)
  let L:= scope (fun i:slotC G (sizeQ C k)=>Finsupp.single (calls wide i) 1) K
  let M:=milk L W
  let p0:=contracted R d wide E W
  have hid:milk K (rename (calls wide) W)=rename (calls wide) M:=by rw [Normal.labelled];exact Normal.prepared ..
  have hp:p0=trim (printed0 wide d M) (key G d) d:=by dsimp only [p0,contracted];rw [hid];rfl
  have oriented:Spirit M:=intact L (good.1 wide).orients spin
  let f:= (Subtype.val : KeyIn G d → Key G)
  have ht:rename f p0∈localFields G d:=by rw [hp];exact roots_seed M wide d oriented
  let Z:Label G d:=⟨_,ht⟩
  let y:=F.coords Z
  have hy:expose F y=p0:=by rw [expose_at,show F.coords.symm y=Z from F.coords.symm_apply_apply Z];apply rename_injective (R:=ℂ) (f:=f) Subtype.val_injective (returns Z)
  refine ⟨y,hy,?_⟩
  have time:t=(Lev).clock.threshold k:=by unfold t;rw [show ((C).path.rep N p k).p=(Lev).budget k from (R.makes.wilson.represents N p k hk).vac]; rfl
  have gh:0<g:=inv_pos.mpr (Real.sqrt_pos.2 (Overlay.beta_positive R.makes.wilson hk))
  have th:0<t:= ((C).path.rep N p k).p.threshold_pos
  have zn:(↑(t/g):ℂ)≠0:=by exact_mod_cast (div_pos th gh).ne'
  have zn':(↑(g/t):ℂ)≠0:=by exact_mod_cast (div_pos gh th).ne'
  have invs:factors (↑(t/g):ℂ) (rename (calls wide) W)=rename (calls wide) (dustAt live q):=by
    dsimp only [W,Spindle.sender]
    rw [show t/g=(g/t)⁻¹ by rw [inv_div],Normal.labelled,sprinkle,Complex.ofReal_inv]
    exact congrArg _ (cycles (fun _=>1) _ zn' _)
  change thawKey (F.coords.symm (F.scaled (t/g) y))=_
  rw [weighed_in,←expose_at,hy]
  change factors (↑(t/g):ℂ) (trim (exchange _ (milk K (rename (calls wide) W))) _ _)=_
  rw [←trim_factor,sprinkle,blend_up _ _ zn,invs]
  change _=trim (exchange _ (milk (opq K (↑((Lev).clock.threshold k/g):ℂ)) _)) _ _
  rw [←time]

end YM.Integration.WilsonThermometerWeakGroupCoordinate
end
