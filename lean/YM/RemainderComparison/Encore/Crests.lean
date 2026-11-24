import YM.RemainderComparison.Encore.Voice
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Encore
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset Solos Lyric Mosaic Serif Marker GridRenewal.Rain
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {L f c : Side} {R:Rep G f}{S:StepData c f}
variable {θ ι:Type} [DecidableEq θ]{J:Marker.Census θ}
variable (M:ι→Lotus.Leaf R)(U:Config G f)(B:Set ι)(l:ι→ℝ)(z:ι→Marker.Poly J)
-- Input log terms REAL * amplitude* and incoming cost.B. Only require uniqueness for occupied logs (fresh padding possible).
variable (B:Set ι)(l:ι→ℝ)(z:ι→Marker.Poly J)
local notation "Vʼ"=> Mosaic.raw M
local notation "Φ"=> primitive M U B l z
local notation "Y"=> Anc (J:=J) (R:=R) U
local notation "κ"=> limb M
local notation "A"=> R.activities
local notation "B₀"=> (Real.exp (R.exponent U))
set_option quotPrecheck false
local notation "n"=> Drums M S

def arrow (s:Finset ι)(k:Finset ℕ) := if (A).admissible R.p U k then Encore.chop κ Φ Y s k else 0
local notation "Dx" => Encore.arrow M U B l z
variable (d : Marker.Census θ) -- shadow
variable {w:θ→ℝ} {t p μ σ D α : ℝ} {k:ℕ}(h : R.Lawful σ t p μ D)
variable (he:∀ i,0<w i)(hp:Summable (fun i=>Marker.Poly.price w (Encore.primitive M U B l z i)))
include h he hp
lemma earnings : Summable (fun i: Finset ι× Finset ℕ=> Dx i.1 i.2):=by
    let f i:= chop κ Φ Y (i:Finset ι×Finset ℕ).1 i.2; have ht: Summable f:=by
        obtain ⟨g,hg,hR⟩:= R.activities.K_total h.labels.boundK; refine tally κ Φ Y he hp (Summable.of_nonneg_of_le (fun _=> Marker.Poly.nonnegative he _) ?_ hg)
        intro i; unfold Anc; rw [Marker.Poly.adapted,Marker.Poly.one_price,mul_one,Complex.norm_real]; exact (hR i).2 U
    apply Summable.of_norm_bounded ht.norm; intro i; unfold Encore.arrow; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
omit he hp
lemma includes (v:Lyric.Drums M S) : (Vʼ v|>.paint B l z U)= Complex.ofReal (B₀) • (∑' k:Finset ℕ, Dx v.val k):=by
    let E:= team M v; have hh:= Team.bud E h|>.summable U; unfold arrow; simp_rw [Encore.cares]
    let f i:= (E.bun i U); let r:= (Vʼ v).stock l; let c:= Verse.controls B z (Vʼ v|>.letters)
    have hv : Summable (fun k=> (↑(r * f k):ℂ)) := Complex.ofRealCLM.summable (hh.mul_left r)
    -- tsum scalar migration (real, not normed θ)
    change _ = Complex.ofReal (B₀) • (∑' k,(↑(r*f k):ℂ) • c); rw [hv.tsum_smul_const, smul_smul, ← Complex.ofReal_tsum] -- edit
    unfold Verse.paint Verse.emit Mosaic.raw Team.cicada; dsimp only; change ((↑(r* (B₀*(∑' k,f k))):ℂ)) • c=_
    rw [Summable.tsum_mul_left r (show Summable f from hh),← Complex.ofReal_mul,mul_left_comm]

variable (hs:doors M)
variable [Fintype θ]
-- add calibrated exponents η estimated via real E. width.
include hs he hp
lemma aperture (u :ι→Marker.Poly J)(hu:Summable u)(hv:∀ i,cyclone (u i)= if limb M i=none then 1+ Φ i else 1) (q:Finset ℕ):
    ∑' p:n,Dx p.val q= if R.activities.admissible R.p U q then cyclone (∑' i,u i)*∏ i∈q,eatS κ Φ Y i else 0 :=by
    unfold arrow; split_ifs; next ht=>
       have ht': Summable (fun i=> Marker.Poly.price w (Y i)):=by obtain ⟨g,hg,hR⟩:= R.activities.K_total h.labels.boundK; refine hg.of_nonneg_of_le (fun _=>Marker.Poly.nonnegative he _) ?_; intro i; unfold Anc; rw [Marker.Poly.adapted,Marker.Poly.one_price,mul_one, Complex.norm_real]; exact (hR i).2 U
       refine (tsum_subtype_eq_of_support_subset (show Function.support (fun p=>chop κ Φ Y p q) ⊆ {p:Finset ι| Set.InjOn (sign M S) p} from ?_)).trans (Encore.alive κ Φ Y he hp ht' q u hu hv)
       intro i hi; apply Encore.funded _ hs i; by_contra h; exact hi (show _ from if_neg (show ¬ (unique κ i ∧ token κ i⊆q) from fun H=> h H.1)) -- `n` definitional.
    next=> exact tsum_zero

-- star mark. K product doesn't insist positivity for any z. flags for each.
def gas (q : Finset ℕ):= if (A).admissible R.p U q then ∏ i∈q,eatS κ Φ Y i else 0
local notation "X"=> gas M U B l z

-- ACT.Steps after exact tuning. Need Retain Cosmos
local instance : IsTopologicalSemiring (Marker.Poly J) where
lemma thole (a:ℝ)(hl:ι→ℝ) (hL:l= Muse.sits B hl a) (u :ι→Marker.Poly J) (hu:Summable u) (hv:∀ i,cyclone (u i)= if limb M i=none then 1+ Φ i else 1) :
         Serif.TuneR M B hl a z S U= Complex.ofReal (B₀) • (cyclone (∑' i,u i) * ∑' q,gas M U B l z q):=by
    let W p:= Dx (p:n× Finset ℕ).1.val p.2
    have hx : Summable W:= (earnings M U B l z h he hp).comp_injective (i:=fun i:n × Finset ℕ=>(i.1.val,i.2)) (fun i j he=>Prod.ext (Subtype.ext (congr_arg Prod.fst he)) (congr_arg (Prod.snd (α:=Finset ι) (β:=Finset ℕ)) he))
    have ht q: ∑' p:n,Dx p.val q= cyclone (∑' i,u i)*gas M U B l z q:=by rw [Encore.aperture M U B l z h he hp hs u hu hv q]; unfold gas; split; rfl; simp
    have hJ: Summable (fun k=> ∑' i:n,W (i,k)):= hx.prod_symm.prod
    have hT:Summable X:=by
        let L:=∑' i,u i; apply (hJ.mul_left (cyclone (-L))).congr; intro i; change cyclone (-L)*(∑' p:n,Dx p.val i)=_; rw [ht,←mul_assoc,← GridRenewal.Rain.plus, show -L+∑' i,u i =0 from neg_add_cancel L]; simp
    unfold Serif.TuneR; rw [←hL]; simp_rw [includes M U B l z h]; rw [Summable.tsum_const_smul _ (show Summable (fun i:n=> ∑' k,Dx i.val k) from hx.prod), ← Summable.tsum_comm (f:=fun i:n=> Dx i.val) hx]; congr 1
    simp_rw [ht]; exact hT.tsum_mul_left _
end YM.RemainderComparison.Encore
