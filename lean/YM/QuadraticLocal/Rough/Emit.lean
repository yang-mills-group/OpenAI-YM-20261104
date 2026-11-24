import YM.RemainderComparison.Serif.Stage
import YM.QuadraticLocal.Rough.Premium
/-!
# Uniform issue law on any Census, including high replication

The payer hΩ and hT (using high l at probes) are the additional
requirements of the rough advance. k-budget from the *other* sharp
payer hZ here **any** arity in this volume. The identity used doesn't
credit any marker cost over the contour in ν`. Keep actual K.

 Replay of the `Serif.Stage`+ earlier proofs. No Census-count argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Serif
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (l:ι→ℝ) (δ:ℝ)
open Verse Marker Script
variable {β:Type} [DecidableEq β]{Jm:Census β}
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "L₁"=> Muse.song M H χ U.V (∅:Set ℕ) 0
local notation "P₀"=> tax G L x

local notation "Zℓ"=> (Set.univ : Set ι)
local notation "Lt"=> sits Zℓ l δ
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto M l δ H τ K Y I)
variable (z:ι→Poly Jm) {fP:β→ℝ} {kZ:ℕ}(hZ: Chorus Jm fP Set.univ z kZ)
open Mallow Ovens Progress.DirectedRecipe
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)(P':BudgetPoint) (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)

local notation "VB" => Refrain.read H' D χ E₀ V₀
local notation "f'"=> Refrain.visa H' D


variable {φ:ℝ} (hpF:1≤φ)(hΩ:Motto M (Lyric.mulScale (Y*φ) l) 0 H τ K Y I)(hT : Glit.LeasePlot M H l Y τ)
local notation "E'"=> jewel M H χ
include h hZ hh
lemma inputFree : Dominated (fun i:Drums M S=> (raw M i).paint Zℓ Lt z) :=by
   have hp:δ≤ 1:= (le_mul_of_one_le_left hh.positive h.allowed).trans hh.emit
   have ht:= Serif.league M H l δ hh; obtain ⟨X,hX,sx,t',hl⟩:= hh.claim
   have he (i) :0 ≤ sits Zℓ l δ i:= mul_nonneg (show 0 ≤ Verse.marked (Zℓ)ᶜ δ i from (by unfold Verse.marked; split; exact hh.positive; exact zero_le_one)) (hl.currency i)
   apply dominion M H Zℓ _ z hZ _ he
   exact ht.of_nonneg_of_le (fun i=> mul_nonneg (he i) (Leaf.profit _) ) fun i=> mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hl.currency _) (show Verse.marked (Zℓ)ᶜ δ i ≤ 1 from by unfold Verse.marked; split; exact hp; exact le_rfl)) (Leaf.profit _)

open Daisy

-- Visibility from *fixed* Book: test owner willing to pay from envelope === genuine Poly
variable (Sx : BudgetPoint) (hx:Sx.B=radiusB x)(hv:Sx.threshold=Pressure.temp x)(ht:Sx.order≤j)(hJ:Sx.power≤J)
include hpF hΩ hx hv ht hJ
lemma rollFree : ∃ c':Staff M H→ℝ, Summable c' ∧ ∀ i:Staff M H,∀ V:Config G c, Poly.price fP ((E' i.fst i.snd).paint Zℓ Lt z V) ≤ c' i := by
   have hs₁: Lt=l:= by ext; simp [sits,Verse.marked]
   rw [hs₁]; let A : Set (Staff M H):= Set.univ; let fm:=( Muse.toll M H l (Muse.song M H χ U.V ∅ 0) j J ); let hi:= Glit.fℓ M H χ l U h hpF hΩ Sx hx hv ht hJ|>.1
   let sm (i:Staff M H):=if i∈A then fm i else 0; have hw i:0≤ sm i:=by simpa [sm,A,fm] using ((hi.mark i (Set.mem_univ _)).nneg);
   exact ⟨sm,Daisy.Charity.everyoneN _ _ hw (show Ac.Hit (Sleet.Base M H) (radiusB x) sm a γ from (by rw [← hx]; simpa only [sm,fm,A,Set.mem_univ,↓reduceIte] using hi.costs)) (fun i _=>educt M H i) h.price.visit.posts, fun i y=> (Serif.housing hZ _ _ _).trans ((Serif.shrine M H χ l Sx hi hv i (Set.mem_univ _) y).trans_eq ((show fm i= sm i from (by unfold sm; simp only [A,Set.mem_univ,↓reduceIte]))))⟩
omit hx hv ht hJ hpF hΩ
include hT
lemma rollAll : ∃ c': (Σ i:Refrain.Leaf H,KEntry M H i) → ℝ,Summable c' ∧ ∀ i t Y, Poly.price fP ((Mosaic.parade M H χ i.val t).paint Zℓ Lt z Y)≤ c' ⟨i,t⟩:=by
    have hd : ∀ i:Refrain.Leaf H,(H.library i.val).Nonempty:=by
       intro i; obtain ⟨j,hj⟩:=i.prop -- inventory subset
       obtain ⟨x,hx,hm⟩:=mem_biUnion.mp hj; -- x is Thick. chapterFoot.nonempty
       exact Finset.Nonempty.mono (subset_biUnion_of_mem H.bookFoot (mem_toLeft.mp hx)) (Refrain.chapter_ne H _)
    let t: (Σ i:Refrain.Leaf H,KEntry M H i) ↪ Flak M H:= Embedding.sigmaMap (Embedding.subtype _) (fun i=> Embedding.refl (KEntry M H i))
    let u(i):=Bank M H l (t i).1 (t i).2; have hC i V: ‖( Mosaic.parade M H χ (t i).1 (t i).2 ).emit l V‖ ≤ u i:= Glit.security M H χ l U h hT (t i) V
    have ht i:0≤u i:= (norm_nonneg _).trans (hC i 1);
    refine ⟨u,Daisy.Charity.everyoneN _ _ ht ((show Ac.Hit (fun i=> H.library (t i).fst) (radiusB x) u a _ from fun i=> budget_pull t t.injective (Glit.weather M H χ l U h hT i))) (fun i _=> hd i.1) h.price.visit.posts,fun i z' y=>?_⟩
    rw [ (show Lt=l from (by ext; simp [sits,Verse.marked])) ]; exact (housing hZ _ _ _).trans (hC ⟨i,z'⟩ y) -- inference
include hpF hΩ hx hv ht hJ
omit hT in
lemma topFull (V':Config G c): let t:=fun i=>glyph M H χ Zℓ l δ z i V'
   Summable t ∧ Tendsto (fun s:Finset ι=>∑' i,branch M H χ Zℓ l δ z s i V') atTop (𝓝 (∑' i,t i)):=by
   intro f; obtain ⟨t,hP,hV⟩:= rollFree M H χ l δ U h hh z hZ hpF hΩ Sx hx hv ht hJ
   obtain ⟨C,hC,hQ⟩:= Poly.equivalent_norm (R:=Jm) hZ.votes
   have hp:Summable (fun i=>‖f i‖):= (hP.mul_right C).of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> (hQ _).trans (mul_le_mul_of_nonneg_right (hV ..) hC))
   have he (p:Finset ι): (∑' i,branch M H χ Zℓ l δ z p i V')=∑' j,f (grid M H p j):=by
      rw [show _= _ from ((hp.comp_injective (grid M H p).injective).of_norm (f:= (fun j=>f ((grid M H p) j)))).tsum_sigma]; -- syntax
      apply tsum_congr; intro i; rw [junction,tsum_fintype]
   refine ⟨hp.of_norm,?_⟩; simp_rw [he]; exact tend (grid M H) f hp (Script.roam M H)
omit hx hv ht hJ hpF hΩ
local notation "FR"=> foible M H χ Zℓ l δ z H' D
local notation "BR"=> book M H χ Zℓ l δ z H' D P' E₀ V₀
local notation "TR"=> tome M H χ Zℓ l δ z H' D P' E₀ V₀
variable (V:Config G c)
local notation "MX" p=> M ∘ Script.restrict p
lemma stationFull : (∀ i, Tendsto (fun p=> FR p V i) atTop (𝓝 (Lane M H χ Zℓ l δ z H' D V i)))∧
     ∃ u:ℕ→ℝ,Summable u∧ (∀ i,0 ≤ u i)∧
       ∀ i p, Poly.price fP (FR p V i) ≤ u i:=by
    obtain ⟨W_,hw,hW⟩:= Serif.rollAll M H χ l δ U h hh z hZ hT
    have hw' i : Summable (fun w:Scene M H (i:Refrain.Leaf H).val=> W_ ⟨i,w⟩):= hw.sigma_factor i
    let u i:= ∑' p:Scene M H (i:Refrain.Leaf H).val,W_ ⟨i,p⟩
    have hz i w:0≤ W_ ⟨i,w⟩:= (Poly.nonnegative hZ.votes _).trans (hW i w V)
    have hp':Summable u:= hw.sigma
    have he (i) (hp:i∉ Set.range f'): Tendsto (fun p=>FR p V i) atTop (𝓝 (Lane M H χ Zℓ l δ z H' D V i)) ∧ ∀ p, FR p V i=0:=by
       have ht (p:Finset ι): FR p V i=0:=by unfold foible; unfold Mosaic.showK; rw [Progress.DirectedRecipe.blank _ _ hp]; rfl
       simp_rw [ht, Lane, Progress.DirectedRecipe.blank _ _ hp]; exact ⟨tendsto_const_nhds,fun _=>trivial⟩
    constructor
    · intro i; by_cases hx:i∈Set.range f'
      swap; · exact (he i hx).1
      obtain ⟨w,rfl⟩:=hx; let f i:= (Mosaic.parade M H χ w.val i).paint Zℓ Lt z V; have hs : Summable (fun i=> ‖f i‖):=(show Summable f from (Poly.budgeted hZ.votes (hw' w) (fun i=>hW w i V)).1).norm -- Summable.norm possibly implicit ℝ Banach FD
      rw [Lane,stuffed]; have hu (p:Finset ι): FR p V ((f') w)=∑' i:Scene (M ∘ Script.restrict p) H w.val,f ((Script.queue M H (Script.restrict p) w.val) i):=by rw [Serif.visits,tsum_fintype]
      simp_rw [hu]; exact Serif.tend (fun i=>Script.queue M H (Script.restrict i) w.val) f hs (fun i=>Script.flags M H w.val i)
    let p:=Refrain.visa H' D; have ht:Summable (stuff p u):= (p.injective.hasSum_iff (fun i hp=>Progress.DirectedRecipe.blank _ _ hp)).1 (show HasSum (stuff p u ∘ p) _ from hp'.hasSum.congr_fun (fun i=>stuffed ..))|>.summable
    refine ⟨stuff p u,ht,fun i=>?_,fun i P=>?_⟩
    · by_cases h:i∈ Set.range p
      · obtain ⟨j,rfl⟩:=h; rw [stuffed]; exact tsum_nonneg fun i=>hz ..
      rw [Progress.DirectedRecipe.blank _ _ h]
    by_cases hv:i∈ Set.range p
    swap; · rw [(he i hv).2 P,Progress.DirectedRecipe.blank _ _ hv,Poly.zero_price]
    obtain ⟨i,rfl⟩:=hv; unfold p; rw [stuffed,visits]; apply le_trans (Poly.batch hZ.votes ..)
    refine le_trans (sum_le_sum (fun j _=> hW i (queue M H (Script.restrict P) _ j) V)) ?_
    let f (w:Scene M H i.val):=W_ ⟨i,w⟩; exact le_trans (show _ ≤ ∑ w∈univ.map (queue M H (Script.restrict P) i.val), f w from by rw [Finset.sum_map]) ((hw' i).sum_le_tsum _ (fun i _=> hz ..))
lemma ledgerFull : Tendsto (fun p=> ∑' i,TR p V i) atTop (𝓝 (∑' i,BR V i)) ∧ Summable (BR V):=by
   obtain ⟨hx,b,hb,he,h⟩:= Serif.stationFull M H χ l δ U h hh z hZ H' D hT V
   obtain ⟨c,hc,hK⟩:= Poly.equivalent_norm (R:=Jm) hZ.votes
   let a (i:Finset ℕ):= (∏ j∈i,b j)*c
   have hp p i : ‖TR p V i‖ ≤ a i:=by
       unfold tome Merge.Photo.fronts; split
       · apply (hK _).trans; exact mul_le_mul_of_nonneg_right ((Poly.multiple hZ.votes ..).trans (prod_le_prod (fun _ _=> Poly.nonnegative hZ.votes _) (fun _ _=> h ..))) hc
       rw [norm_zero]; exact mul_nonneg (prod_nonneg fun i _=>he _) hc
   have ht i:Tendsto (fun p=> TR p V i) atTop (𝓝 (BR V i)):=by
      unfold book tome Merge.Photo.fronts; split_ifs; · exact tendsto_finsetProd _ fun i _=>hx i
      exact tendsto_const_nhds
   have hz:Summable a:=(summable_finsetProd_of_summable_nonneg he hb).mul_right _
   exact ⟨tendsto_tsum_of_dominated_convergence hz ht (Eventually.of_forall hp), (Summable.of_norm (hz.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> le_of_tendsto ((ht i).norm) (Eventually.of_forall (fun j=>hp j i)))))⟩
local notation "TU" => TuneR M Zℓ l δ z S
local notation "Qf"=> Quota M Zℓ l δ z S
include h hh hZ
omit hT in
lemma chaseFull [Countable ι] : Tendsto (fun p=> S.push R.beta (Qf p) V) atTop (𝓝 (S.push R.beta TU V)):= by
   have hv:= Serif.inputFree M H χ l δ U h hh z hZ
   obtain ⟨t,hp,hF⟩:= hv
   let f i:= (raw M (i:Drums M S)).paint Zℓ (sits Zℓ l δ) z
   have hz : S.IsKernel R.beta G:= S.isKernel (funds_branch H.laws.intake.ready) _
   let Z_ i X:= S.density R.beta X V • f i X
   have ht (p): Integrable (Z_ p) (prior G _) :=by
     refine StepData.push_slice hz V _ ?_; unfold f; exact ((((team M p).sells H.laws.intake.cap).1.integrable _).const_mul ((raw M p).stock Lt)).smul_const (Verse.controls Zℓ z (raw M p).letters)
   obtain ⟨a,ha⟩:=hz.bound
   have hb i:0≤t i:= (norm_nonneg _).trans (hF i 1)
   have he i X: ‖Z_ i X‖ ≤ a*t i := by
      unfold Z_; rw [norm_smul,Real.norm_of_nonneg (hz.positive ..)]
      exact mul_le_mul (ha ..) (hF ..) (norm_nonneg _) ((hz.positive ..).trans (ha X V))
   have hpP:Summable (fun i=> ∫ x, ‖Z_ i x‖ ∂prior G _):= by
     apply (hp.mul_left a).of_nonneg_of_le (fun i=> integral_nonneg fun _=>norm_nonneg _); intro i
     apply le_trans (integral_mono (ht i).norm (integrable_const (a*t i)) (he i)); simp
   have hk := hasSum_integral_of_summable_integral_norm ht hpP
   have hpV(X): (∑' i,Z_ i X)=S.density R.beta X V • TU X:= by
      exact ((hp.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>hF i X)).of_norm.tsum_const_smul (S.density R.beta X V))
   simp_rw [hpV] at hk; let g i := ∫ x,Z_ i x ∂prior G _
   have hQ (p:Finset ι): S.push R.beta (Qf p) V= ∑' j,g (Script.drums M (Script.restrict p) S j):=by
      let h:=Script.drums M (Script.restrict p) S; have he(X): S.density R.beta X V • (Qf p X)=∑ j:Drums (M ∘ Script.restrict p) S,Z_ (h j) X:=by
         unfold Quota TuneR; rw [tsum_fintype,Finset.smul_sum]; refine sum_congr rfl fun i _=> ?_; unfold Z_ f h; rw [Script.docket,Script.letter,Script.clears]
      unfold StepData.push; simp_rw [he]; rw [integral_finsetSum (Finset.univ) (fun i _=>ht (h i)),tsum_fintype]
   rw [show S.push R.beta TU V=∑' i,g i from hk.tsum_eq.symm]; simp_rw [hQ]; exact Serif.tend _ g (show Summable (fun i=>‖g i‖) from hk.summable.norm) (Script.arrived M)

variable [Fintype β]
variable (hx₀:P'.B=radiusB x) (hp:P'.threshold=Pressure.temp x)(ht₀:P'.order≤j)(hk:P'.power≤J) (hf:P'.supportExponent≤a)
include hx₀ hp ht₀ hk hf hpF hΩ hT

lemma emitted [Countable ι] (X:Tree.Forest S.ratio) :
    let F i := Serif.glyph M H χ Zℓ l δ z i V
    Summable F ∧ Summable (BR V) ∧
    S.push R.beta (TU) V= (Complex.ofReal (overhead (prism T x χ o.K V X) R Q.table)) • (GridRenewal.Rain.cyclone (∑' i,F i) * ∑' i,BR V i):= by
   intro FF
   let v:Finset ι→Poly Jm:= fun p=> S.push R.beta (Qf p) V
   have hy:= Serif.chaseFull M H χ l δ U h hh z hZ V
   obtain ⟨hF,hV⟩:=Serif.topFull M H χ l δ U h hh z hZ hpF hΩ P' hx₀ hp ht₀ hk V
   obtain ⟨hQ,hS⟩:= Serif.ledgerFull M H χ l δ U h hh z hZ H' D P' E₀ V₀ hT V
   let a:ℂ:= overhead (prism T x χ o.K V X) R Q.table
   refine ⟨hF,hS,tendsto_nhds_unique hy ?_⟩
   refine Tendsto.congr' ?_ (((GridRenewal.Rain.breath.continuousAt.tendsto.comp hV).mul hQ).const_smul a)
   refine Eventually.of_forall fun p=>?_ ; let g:= Script.restrict p; let Z':=(g) ⁻¹' Zℓ
   have hp' := Muse.step (MX p) H χ F' Z' (l ∘ g) δ h.price (Muse.enrolled _ _ _ Z' _ _ U h (Script.scaled M H _ l δ hh)) H' D P' E₀ V₀ hp hx₀ hf (z ∘ g) (fun i=>hZ.square (g i)) X V
   change _= v p; have hv : Qf p=fun X=> ∑ i:Drums (MX p) S,(raw (MX p) i).paint Z' (sits Z' (l∘g) δ) (z∘g) X:=by
      funext V; unfold Quota TuneR; rw [tsum_fintype]
   unfold v; rw [hv]; exact hp'.2.2.symm

end YM.RemainderComparison.Serif
