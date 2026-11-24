import YM.Gaps1020.Local.MarkedRevenue
import YM.MergeProof.Sate
/-!
# Nonempty marker modes in thermal E

Work on THE ACTUAL nilpotent algebra of simultaneous markings; same
representation as shipped `Palette` kernel. Non-empty tags only. Formula
keeps each combination of tags & grades. Can later take tally while
retaining support at all contributing origins. Off Healthy each cost assertion
is only on the persistent germ – physically it is the `masked` value.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
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
variable (N:Captain H j C' d v Y A b r B q k χ)(U:ι→Team R)(M':ι→Leaf R)
    (rA:ι→ℝ)(X:Utopia H j v d r C' χ)
local notation "I'" => Tickets (Palette.sign M' S)
open Marker Merge.Switch Gas Ursell Captain Push.GridApprox.Nil
variable (χ)
variable {M:ℕ}
abbrev Sections := I' × Orders M -- order indep S? syntax
abbrev Requests (p:H.fragrances):= Option (Fin p.1) → Sections (S:=S) M' (M:=M)
def aggregateGrade (p:H.fragrances)(i:Requests M' p (M:=M)): ℕ:= ∑ j, ((i j).2:Orders M).val
variable {χ}
def rung (χ:Chi)(p:H.ThinP)(j:I'× Orders M)(V:Config G c):ℝ:= scalarWeight rA j.1*sliceMix H χ M p (Palette.team M' j.1) j.2 V
def quantity (χ:Chi)(p:H.fragrances)(i:Requests M' p (M:=M))(V:Config G c):ℝ:= (coefficient H.seam p.snd / (p.fst+1).factorial) * ∏ j, rung M' rA χ (p.2 j) (i j) V
variable {V':Type}[DecidableEq V']{E':Marker.Census V'}
variable (g:ι→Poly E')
def letter (p:H.fragrances)(i:Requests M' p (M:=M)): Poly E':= ∏ j,∏ a∈ (i j).1.val,g a
def forecast (χ:Chi)(p:H.fragrances)(take : ℕ→Prop)(i:E'.Mode): Config G c→ℂ:=
     ∑ q ∈ (univ : Finset (Requests M' p (M:=M))).filter (fun q=>take (aggregateGrade M' p q)),
        (letter M' g p q).part i • (Complex.ofReal ∘ quantity M' rA χ p q)
lemma forecastAll (χ:Chi)(p:H.fragrances)(u:E'.Mode)(take:ℕ→Prop): forecast M' rA g χ p (M:=M) (fun _=>True) u= forecast M' rA g χ p (M:=M) take u+forecast M' rA g χ p (M:=M) (fun i=>¬take i) u:=by
   unfold forecast; simp only [Finset.filter_true]; rw [Finset.sum_filter_add_sum_filter_not]
-- proof at knot even for nonhealthy addressing. masks apply to union-of-head
-- configurations, no term escaped via a split without the mask.
variable (z:H.fragrances) (hV:∀ i,g i*g i=0)(U:Config G c)(hc:Thermal.BuysMix M' H rA)
local notation "Lℓ" => reachability z
local notation "ψ" => sound g
private lemma sounding (p:H.ThinP) : ψ (vote M' H χ rA p.val U)= ∑ i:I',((scalarWeight rA i * Palette.act M' H χ U p.val i:ℝ):ℂ) • ∏ j∈i.val,g j:=by
    let c(i:I'):= scalarWeight rA i * Palette.act M' H χ U p.val i; let a (i:I'):= click i.val (c i)
    have h: vote M' H χ rA p.val U=∑ i,a i:=by
       ext t v; simp only [Finset.sum_apply]; unfold vote Palette.color; apply sum_congr rfl; intro i _; rw [amplitudes]; unfold a click c scalarWeight; split <;> ring
    rw [h, Switch.summed g univ a (fun i=>‖c i‖) (fun i _=> paidClick _ (norm_nonneg _) (fun _=>le_rfl))]; exact sum_congr rfl fun i _=> Switch.gather ..
include N
omit [Fintype ι] in
private lemma reveal (p:H.ThinP)(i:I') : Palette.act M' H χ U p.val i = masked (Pressure.temp s) (H.smallAt p) (preserved H χ p (Palette.team M' i)) U:=paysTeam p _ N _
private lemma stamped (p:H.ThinP)(M:ℕ)(hp: Healthy (Pressure.temp s) (H.smallAt p) U): ψ (vote M' H χ rA p.val U)= ∑ i:I' × Orders M, (↑(rung M' rA χ p i U):ℂ) • ∏ j∈i.1.val,g j :=by
    rw [sounding,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; dsimp only; rw [reveal N M' U p i,masked_eq _ _ _ _ hp]; unfold rung; dsimp only; rw [← recoversMix p _ U M,Finset.mul_sum,Complex.ofReal_sum,Finset.sum_smul]

omit N
private lemma metronome : song M' H χ rA z U=(fun _ (_:Finset ι)=> coefficient H.seam z.2/↑(z.1+1).factorial) * (∏ i:Option (Fin z.1),vote M' H χ rA (z.2 i).val U):=by
   ext t u; simp only [Pi.mul_apply,Finset.prod_apply]; unfold song Cash.trainedMill Gas.term; unfold Cash.entriesMill vote; ring
include hc hV N
lemma stampRevenue (M:ℕ) : ψ (song M' H χ rA z U)= masked (Pressure.temp s) (Lℓ) (fun V=> ∑ i:Requests M' z (M:=M), (↑(quantity M' rA χ z i V):ℂ) • letter M' g z i) U:=by
   let v i:= vote M' H χ rA (z.2 i).val U; let x:= coefficient H.seam z.2/↑(z.1+1).factorial; let I:=univ (α:=Option (Fin z.1)); let f(i):= ∏ j∈(z.2 i).val,Palette.toll M' H rA j
   have ht i:Paid (fun _:Unit=> v i) (f i):= Paid.toPoint _ (payments M' H χ rA hc.nonnegative (z.2 i).val) U
   obtain ⟨u,hu⟩:= (Paid.prod I _ _ (fun i _=> ht i)).works (); rw [Finset.prod_apply] at hu
   have hs (t:ℝ): Models (fun (_:ℝ) (_:Finset ι)=>x) (fun _=>bench ∅ x):= by have h:=(modelClick (ι:=ι) ∅ x); convert! h using 1; ext; simp [click]
   rw [metronome, mul_sounds g hV (hs 0) hu,const_sounds, Switch.product g hV I v f (fun i _=> ht i),Poly.product_bead]
   by_cases hp: Healthy (Pressure.temp s) (Lℓ) U
   swap; · have hh: ∃ i, ¬Healthy (Pressure.temp s) (H.smallAt (z.2 i)) U:=by by_contra! hn; apply hp; refine Finset.disjoint_left.mpr (fun i hi h=>?_); obtain ⟨j,hj,h'⟩:=mem_biUnion.mp hi; exact Finset.disjoint_left.mp (hn j) h' h
           obtain ⟨i,h⟩:=hh; rw [masked_ne _ _ _ _ hp,prod_eq_zero (s:=I) (f:=fun i=>ψ (v i)) (mem_univ i), smul_zero]; unfold v; rw [sounding]; apply sum_eq_zero; intro j _; rw [reveal N M' U (z.2 i) j, masked_ne _ _ _ _ h]; simp
   rw [masked_eq _ _ _ _ hp]; unfold v
   simp_rw [fun i=> stamped N M' rA g U (z.2 i) M (show Healthy _ _ _ from Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ i)) hp)]
   unfold I; rw [Fintype.prod_sum (f:=fun i (j:Sections (S:=S) M' (M:=M))=> (↑(rung M' rA χ (z.2 i) j U):ℂ) • ∏ k∈j.1.val,g k), Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [Finset.prod_smul,smul_smul,← Complex.ofReal_prod,← Complex.ofReal_mul]; rfl
lemma met (M:ℕ)(u:E'.Mode)(hu:u≠E'.quiet): (Photo.headSheet M' H χ rA E' g z U).part u= masked (Pressure.temp s) (Lℓ) (forecast M' rA g χ z (M:=M) (fun _=>True) u) U :=by
   let c:= -Palette.song M' H χ rA z U 0 ∅; let v: Ways ι:=fun _ _=> c
   rw [Photo.headSheet, show Photo.tones M' H χ rA z U=song M' H χ rA z U+v from funext fun t=>funext fun p=>sub_eq_add_neg ..]
   rw [Switch.add_sounds _ (show Models (song M' H χ rA z U) _ from ((Palette.fair M' H χ rA (Thermal.allows M' H rA hc) z k).works U).choose_spec) (show Models v _ from ((Paid.works (Switch.constant (fun _:Unit=>c) (norm_nonneg c) (fun _=>le_rfl)) ()).choose_spec)), const_sounds,
       Poly.part_plus, show (Poly.bead E' (↑c)).part u=0 from ?_, add_zero,stampRevenue N M' rA g z hV U hc M]
   · by_cases h: Healthy (Pressure.temp s) (Lℓ) U; swap; · rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,Poly.part_nil]
     rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h];unfold forecast; simp only [Finset.filter_true]; rw [ Finset.sum_apply, Poly.part_sum]; simp only [Pi.smul_apply,Function.comp_apply,smul_eq_mul,Poly.part_smul,mul_comm]
   change (Poly.send _ (↑c)).part u=0; rw [Poly.part_send,if_neg hu]

-- identity pins all marked *forecast* modes. Only needs tag scope (quiet
-- allowed, z escorts uses marker at projected C-foot); forced uses separate.
omit hV N hc
variable (o' : V'→ Site c)[Fintype V']
lemma pins (T₀:ℕ→Prop)(hf:∀ i,Scoped {x| o' x∈ (M' i).crest.image S.ratio.parent} (g i))(u:E'.Mode)(h: ¬ ∀ i∈ u.val,o' i ∈ Lℓ) : forecast M' rA g χ z (M:=M) T₀ u=0:=by
   unfold forecast; apply sum_eq_zero; intro i _; by_cases he : ∀ j, Shared.awake H (z.2 j) (Palette.team M' (i j).1); swap
   · push Not at he; obtain ⟨j,h'⟩:=he; rw [show quantity M' rA χ z i=0 from funext fun V=> by unfold quantity; rw [prod_eq_zero (mem_univ j),mul_zero]; rfl; unfold rung; rw [sleepy (z.2 j) _ h' V (i j).2,mul_zero]]; ext; simp only [Function.comp_apply,Pi.zero_apply,Pi.smul_apply, Complex.ofReal_zero, smul_zero]
   have hS : Scoped {x| o' x ∈ Lℓ} (letter M' g z i):= by
      apply scope_prod; intro j _; apply scope_prod; intro k hk
      let t:= (i j).1; let p:= z.2 j; have hp : t.reach ⊆ p.val:=by rw [← Palette.label]; exact (he j).2.2
      have hz: ((M' k).crest.image S.ratio.parent) ⊆ Lℓ:=by
         intro n hn; apply (show H.smallAt p ⊆ Lℓ from subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ j)); refine Finset.mem_biUnion.mpr ⟨_,hp (t.reaches_of hk),?_⟩
         change n∈ areas R T Q.halo (radiusB s) ((M' k).turn.badge S); rw [Wing.badge_area]; obtain ⟨v,hv,hη⟩:= mem_image.mp hn; refine halo_subset _ _ (mem_image.mpr ⟨v,mem_union_left _ hv,hη⟩)
      exact fun s h=>hf _ _ (fun he=> h (he.trans fun i hi=> hz hi))
   rw [hS u h,zero_smul]
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
