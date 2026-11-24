import YM.FVA1.Fuse
import YM.Gaps1020.Local.Expressed

/-! Consumer on *each actual cash* of the all-grade Mallow.Many transfer. Activating
one separate symbolic marker per leaf puts the Banach/component majorants
upstream of subsequent test substitution (no occupancy hypothesis on these
intermediate marker names -- plot requirement on actual geometry). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA1
open ConnectedActivityE6 Shell Blaze
open Thermal1020 Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
variable {ι:Type}[Fintype ι]
open Merge Palette PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums.Mixed Push.AbsoluteSums.Reserves
open Marker Push.GridApprox.Nil Merge.Photo MergeProof Accent
open Overlay.GapsLocal Trees Captain
variable [DecidableEq ι](M':ι→Leaf R)(rA:ι→ℝ) 

set_option quotPrecheck false
local notation "E'"=> FreeCensus ι
def ink(i:ι) : Marker.Poly (FreeCensus ι):= Poly.send ((FreeCensus ι).fire i) 1
local notation "b'" => (ink (ι:=ι))
local notation "w'" => (1:ι→ℝ)
local notation "ρ'"=> horizonRadius G L s
local notation "Y'"=> fun i=> (M' i).crest.image S.ratio.parent
set_option quotPrecheck false
variable (H:Cash W s μ L Q o C T R)(E0: RG.Rep G c)(K: ℝ→Finset ι→Ovens.Code G c)
  (m:ℕ)(levels:ℕ→Prop)

/-- Assembly in a test-independent alphabet; bins are the actual supported forecast
entries (oscillator jets still use the actual trajectory, not independent formal Wilson).
This encoding is used to supply the hard estimate & support stability through
changes of representation. -/
def cards : Stock (n:=c) ι H.fragrances G where
  X:= reachability (H:=H)
  requires i:= (M' i).crest.image S.ratio.parent
  bin i z:= if z=(FreeCensus ι).quiet then 0 else forecast M' rA b' χ i (M:=m) levels z
  hard:= Photo.Fleece K E' b'
local notation "Y0"=> cards (χ:=Chi.canonical) M' rA H K m levels
variable {B b d a C' v Y r q z' :ℝ}{Γ:Target.Expense Q}{F':RG.Stage}
    (N:Captain H (F':RG.Stage).order C' d v Y a b r B q k Chi.canonical)
    {dk ex:ℝ}(h:Photo.Usable M' H Chi.canonical E0 rA K dk ex (PhysicalNext.Repeat.Mallow.straw μ L G s))
    (hc:Palette.Thermal.BuysMix M' H rA) (ht:Thermal1020.Shared.MixReceipt Γ F' m N)

lemma ink_square (i:ι): ink i*ink i=0:= by
  by_contra he; obtain ⟨z,h,_⟩:=Extra.Trajectories.merges_of_tagged_mul he
  exact Finset.disjoint_left.mp h (mem_singleton_self i) (mem_singleton_self i)
lemma ink_quiet (i:ι): (ink i).part (FreeCensus ι).quiet=0:=by
  rw [ink,Poly.part_send, if_neg (Ne.symm (Marker.Census.fire_hot (FreeCensus ι) i))]

include M' rA h N hc ht
/-- Room for all positions of every leaf (holding an arbitrary one at a time). -/
lemma room_at (he':∀ i, ((M' i).crest).Nonempty) (hP:E0.p.B=radiusB s)(hR:E0.p.order ≤ F'.order):
    (Y0).Room E0 :=by
  let eQ:(i:ι)→ Support c:=Y'
  have hv (o':ι→Site c)(hh:∀ i,o' i∈ eQ i)(i:ι): Scoped {x| o' x∈ eQ i} (ink i) := scope_send _ _ _ (by intro v hv; change v∈({i}:Finset ι) at hv; rw [mem_singleton] at hv; rw [hv]; exact hh i)
  let o':ι→ Site c:=fun i=> S.ratio.parent (he' i).choose
  have hX' (i): o' i∈eQ i:= mem_image_of_mem _ (he' i).choose_spec
  let hK:= Photo.Fleece K E' b'
  have hr(i): Flow o' (MergeProof.barcode E0.activities i) (hK i) E0.p.threshold:= Photo.river M' H Chi.canonical E0 rA K (FreeCensus ι) b' h o' (hv _ hX') i
  have he: Sailor G E0.p.threshold q F'.order:= ⟨fun i v hv=> N.weigh.stroke i v (hv.trans (h.temp.symm ▸ N.talent))⟩
  refine ⟨fun i=> ?_,fun i z=> ?_,fun i=> by simp only [cards,if_true],?_,?_,fun i=>(hr i).home,fun i=>(hr i).turns,fun i=>(hr i).me,?_,?_⟩
  · exact ⟨(Song.locate H i).site,(Song.locate H i).anchor⟩
  · change E0.p.Regular (reachability i) (if z=(FreeCensus ι).quiet then 0 else _); split
    next h=>
      have h:= regular_bound_sum (G:=G) (P:=E0.p) (s:=reachability i) (o:=0) (∅:Finset Unit) 0 0 (fun i hi=> False.elim (notMem_empty _ hi))
      simpa only [sum_empty] using h.1
    next _=> exact (premium N M' rA b' i levels hc ht.shared ht.turns ht.large ht.chargeFits E0.p h.temp hR hP he (Song.locate H i).site (Song.locate H i).anchor m z).1
  · intro i z U hp
    refine atlas_of_each _ z _ (fun y hy j hj _=> ?_)
    change y j ∈ reachability i; by_contra hg
    have ht':∀ i,y i∈eQ i:=fun i=>hy i (he' i|>.image _)
    have hz:= pins M' rA b' i y (M:=m) (χ:=Chi.canonical) levels (hv _ ht') z (fun he=> hg (he j hj))
    apply hp; change ite (z=(FreeCensus ι).quiet) (0:Config G c→ℂ) _ U=_; split; rfl; exact congr_fun hz U
  · exact K0 M' rA b' E0 K ink_quiet h
  · intro i z U hp
    refine atlas_of_each _ z _ (fun y hy j hj _=> ?_)
    by_contra hg
    exact hp ((Photo.river M' H Chi.canonical E0 rA K (FreeCensus ι) b' h y (hv _ fun i=>hy i (he' i|>.image _)) i).scope U z (fun he=> hg (he hj)))
  intro i U hp; by_contra he
  exact hp (fullPass M' rA b' E0 K h i U he)

-- preserve hit budget independent of virtual alphabet. Output regular can even demand stronger
-- support exponent up to Γ.earn at this invocation; K is the limiting one via h, upgrade later via separate K receipt.
lemma lent_at (hf:ℕ)(he:∀ i,levels i → hf ≤ i)(hP:E0.p.B=radiusB s)(hR:E0.p.order ≤ F'.order)
    (hJ:E0.p.power=F'.power) (hB:E0.p.supportExponent≤Γ.earn) :
    (Y0).Lent E0 w' E0.p.supportExponent ((ρ'^hf)⁻¹) (PhysicalNext.Repeat.Mallow.straw μ L G s):=by
    have he': Sailor G E0.p.threshold q F'.order:= ⟨fun i v hv=> N.weigh.stroke i v (hv.trans (h.temp.symm ▸ N.talent))⟩
    have hV(i:ι): 0 < (w') i:=zero_lt_one
    have hw(i:ι):Poly.price w' (ink i)≤1:=by unfold ink; rw [Poly.solo,Poly.solo_toll,norm_one]; exact (mul_one (1:ℝ)).le
    refine ⟨hV,le_rfl,⟨fun i=>priceAt N M' rA b' i levels ρ' m E0.p,fun i z=> price0 N M' rA b' i levels hc _ _ z ((by norm_num: (0:ℝ)≤ 2).trans ht.large), ?_,?_⟩,usableK M' rA b' w' E0 K hV hw h le_rfl⟩ -- extraS refl
    · intro x
      refine budget_loosen (cappedPrices N M' rA b' levels w' hV hw hc m Γ E0.p hP ht.Warn ht.large ht.book ht.meet ht.funds hf he _ hB x) ?_
      apply mul_le_of_le_one_right (by have hz:=ht.large; positivity);
      rw [hJ]; exact ht.expCredit
    intro i z x hx
    change E0.p.supBounds x (reachability i) (if _ then _ else _) _; split
    next hz=>
      have hy:0≤priceAt N M' rA b' i levels ρ' m E0.p z:=price0 N M' rA b' i levels hc m E0.p z ((by norm_num: (0:ℝ)≤2).trans ht.large)
      have hz':= regular_bound_sum (G:=G) (P:=E0.p) (s:=reachability i) (o:=x) (∅:Finset Unit) 0 0 (fun i hi=> False.elim (notMem_empty _ hi))
      have hv:E0.p.supBounds x (reachability i) (0 : Config G c→ℂ) 0:=by simpa only [sum_empty] using hz'.2
      exact ⟨hy,fun U hu l hl hh=> (hv.2 U hu l hl hh).trans hy⟩
    next _=> exact (premium N M' rA b' i levels hc ht.shared ht.turns ht.large ht.chargeFits E0.p h.temp hR hP he' x hx m z).2

set_option maxHeartbeats 400000 in
lemma cash_fused [Nonempty ι](he:∀ i, ((M' i).crest).Nonempty) (hP:E0.p.B=radiusB s)(hR:E0.p.order ≤ F'.order)(hJ:E0.p.power=F'.power)
    (hB:E0.p.supportExponent≤Γ.earn): S.push R.beta (Photo.given (S:=S) M' rA E' b')=
      (cards (χ:=Chi.canonical) M' rA H K m (fun _=> True)).density0 E0:=by
    let st:= cards (χ:=Chi.canonical) M' rA H K m (fun _=>True)
    let eQ:ι→ Support c:=Y'
    let o':ι→Site c:=fun i=> S.ratio.parent (he i).choose
    have hv (i:ι): Scoped {x| o' x∈ eQ i} (ink i) := scope_send _ _ _ (by
      intro v hv; change v∈({i}:Finset ι) at hv; rw [mem_singleton] at hv; subst v
      exact mem_image_of_mem S.ratio.parent (he i).choose_spec)
    have hV(i:ι): 0 < (w') i:=zero_lt_one
    have hw (i):Poly.price w' (ink (ι:=ι) i)≤ 1:=by unfold ink; rw [Poly.solo,Poly.solo_toll,norm_one]; exact (mul_one (1:ℝ)).le
    have hv':= YM.GapsLocal.Full.decideModel (Γ:=Γ) H E0 M' rA b' K o' (0:ι→ℂ) m (0:ℝ) w' N h hc ht ink_square hV hw hv ink_quiet hP hR hJ hB (fun i=>by simp) -- check u' explicit
    let F:=forecast M' rA b' Chi.canonical (H:=H) (M:=m)
    have he'(i:H.fragrances)(u:Said E')(hh:¬pinned o' (reachability i) u): F i (fun _=>True) u.val=0:= pins M' rA b' i o' _ hv u.val hh
    have hx:= hv'.push
    change S.push R.beta (litGiven (S:=S) M' rA b' (0:ι→ℂ)) = _ at hx
    rw [show litGiven (S:=S) M' rA b' (0:ι→ℂ)= Photo.given (S:=S) M' rA E' b' from funext fun U=>by simp [litGiven,Mach]] at hx
    rw [hx]; funext U; unfold Overlay.Bands.density Stock.density0
    congr 2
    · unfold scenery; rw [atAll E0 (reachability (H:=H)) _ _ (fun i=> F i (fun _=>True)) (Photo.Fleece K E' b') he' w' 0 _ _ _ _ hv'.complete.1 hv'.complete.2]
      rw [show (∑ i, Poly.send ((E').fire i) ((0:ι→ℂ) i))=0 from Finset.sum_eq_zero fun i _=> Poly.send_zero _,zero_add]
      apply congr_arg Poly.pass; refine tsum_congr fun i=>?_
      let L:=Finset.univ.filter (fun i:(E').Mode=> i.val.Nonempty); let φ:= (st).glass0 E0 i U
      let g(i:(E').Mode):= Poly.send i (φ.part i)
      change (∑ i':Said E',Poly.send i'.val _) = φ
      rw [Finset.sum_congr rfl (fun (p:Said E') _=>show Poly.send p.val _=g p.val from ?_), ← Finset.sum_subtype L (by simp [L]) g, Finset.sum_subset (f:=g) (Finset.subset_univ L) ?_]
      · exact Poly.studs φ
      · intro j _ hj
        have hh : j=(E').quiet := Subtype.ext (not_nonempty_iff_eq_empty.mp (fun hz=> hj (mem_filter.mpr ⟨mem_univ _,hz⟩)))
        subst j
        unfold g φ st Stock.glass0 cards
        simp only [Poly.part,Poly.inject,if_true]; simp [masked]
      unfold g φ st Stock.glass0 cards
      congr 2
      have hz:p.val≠(E').quiet:=fun he=>p.property.ne_empty (congr_arg Subtype.val he)
      simp only [if_neg hz]; rfl
    unfold Overlay.Bands.cluster; refine tsum_congr fun p=>?_; unfold Overlay.Bands.packet Stock.packet0; split
    next h => exact prod_congr rfl fun j _=> hv'.gas j U
    next _=> rfl

end YM.FVA1
