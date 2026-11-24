import YM.AllOrder.Burn.Whorl
import YM.AllOrder.Burn.Moment
import YM.Progress.DIRECTED_RECIPE.Pellets
import YM.RGComparison01.Marks.Emerson
/-!
# A ribbon for a seed with additional marked addresses

`Pad` assigns a regular address to each site and each of its finite labels.
`Pad.thread` retains the images of the seed and pad addresses. `Pad.roll`
compares the ribbons on two block-related sides when their representation
parameters agree, the radii fit the ribbon bound, and the coarse side has
length greater than four.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Versal
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar Progress.DirectedRecipe RGComparison01 AllOrder AllOrder.Burn AllOrder.Till
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G: Gauge} {c f C F: Side} {W₀:Burn.Locale G} {R:RG.Rep G f} {R':RG.Rep G F}
    {p p' : ℝ} {n b ℓ r k:ℕ}
-- Each site has k distinct labels.
abbrev Names (n:Side)(k:ℕ):=Site n × Fin k
variable {X:Burn.Seed R W₀}
structure Pad (X:Burn.Seed R W₀) (k:ℕ) where
    slip : (Site f × Fin k) ↪ ℕ
    ready (i: Names f k) : R.activities.reg (slip i)=spine R.p i.1
    quiet (i:Names f k): R.activities.E (slip i)=0
    fresh (i:Names f k): slip i ∉ Set.range X.model
namespace Pad
variable (Z:Pad X k)
abbrev Ty (f:Side)(k:ℕ):= Site f ⊕ Names f k
abbrev root : Pad X k→ Ty f k→ Site f:= fun _ i=>i.elim id Prod.fst
noncomputable def map (i:Ty f k):ℕ:= i.elim X.model Z.slip
set_option quotPrecheck false
local notation "Q"=> Pad.map Z
private lemma reg_ext : ∀ v w: RegularAddress f,v.site=w.site → v.support=w.support→v=w:=by rintro ⟨a,b,h⟩ ⟨x,y,H⟩ h1 h2; simp only at h1 h2; subst a; subst b; rfl
lemma paid (n:Ty f k) : R.activities.reg (map Z n)= spine R.p (root Z n):= by
 rcases n with n|n
 · exact reg_ext _ _ (X.reg n).2 (X.reg n).1
 exact Z.ready n
lemma inj : Function.Injective (map Z):= by
 rintro (x|x) (y|y) he
 · exact congr_arg Sum.inl (X.model.injective he)
 · exact False.elim (Z.fresh y ⟨x,he⟩)
 · exact False.elim (Z.fresh x ⟨y,he.symm⟩)
 exact congr_arg Sum.inr (Z.slip.injective he)
variable (h:R.p.B≤ n)
lemma radius (i:Ty f k): (R.activities.reg (map Z i)).support⊆ neighbors (R.p.B) (root Z i):= by rw [paid]; intro q h; exact (neighbors_mem ..).mpr (by simpa only [spine,court,halo_spec,mem_singleton,exists_eq_left] using h)
noncomputable def thread : RGComparison01.Ribbon R n := {
   keep := fun i=> i∈Set.range (map Z)
   ride := fun _=>0
   finite k':= by letI := (Set.finite_range (map Z)).to_subtype; exact Set.toFinite _
   radius i hi:= by obtain ⟨j,rfl⟩:=hi; rw [paid]; intro i hi; apply (neighbors_mem ..).mpr; exact ((neighbors_mem ..).mp (Z.radius j (show _ by rw [paid]; exact hi))).trans h
}
local notation "Th"=> Pad.thread Z h
noncomputable abbrev node (Z:Pad X k)(h:R.p.B≤ n): Ty f k ≃ ((Pad.thread Z h).Node) := Equiv.ofInjective _ Z.inj
lemma tag (i:Ty f k): ((Z.thread h).home (node Z h i))=root Z i:= congr_arg RegularAddress.site (paid Z i)
variable {X':Burn.Seed R' W₀}(Z':Pad X' k)(hK:R'.p.B≤ n) (hF:F.val=f.val*ℓ)
    (hP:R'.p=R.p)
local notation "L"=> Macrame.normal (Deck.divides hF) hF
local notation "Φ"=> (Macrame.normal (Deck.divides hF) hF).cut
-- Project the site to its parent and retain the finite label.
noncomputable def sends (hF:F.val=f.val*ℓ) : Ty F k→ Ty f k:= Sum.map (Macrame.splitter (Deck.divides hF)) (Prod.map (Macrame.splitter (Deck.divides hF)) id)
local notation "τ"=> sends (k:=k) hF
local notation "T"=> (node Z h)
local notation "T₁"=> (node Z' hK)
noncomputable abbrev lower (i:(Pad.thread Z' hK).Node) : (Pad.thread Z h).Node:= node Z h (sends hF ((node Z' hK).symm i))
lemma nest : Deck.Nest (Deck.divides hF) (sends (k:=k) hF) (root Z') (root Z):=by have hx:Deck.Nest (Deck.divides hF) (Φ) id id:= ⟨fun i=>rfl,fun x i hi=> ⟨x,hi.symm,rfl⟩,fun i j _ h=>h⟩; exact hx.sum hx.pr
local notation "M"=> lower Z h Z' hK hF
lemma project_nest : Deck.Nest (Deck.divides hF) (M) (Pad.thread Z' hK|>.home) (Pad.thread Z h|>.home):= by
 have he:= nest Z Z' hF; have hv(i:Ty F k): M (T₁ i)= T (τ i):= by unfold lower; rw [Equiv.symm_apply_apply]
 refine ⟨ fun i=> ?_,fun x i hi=>?_,fun i j hi heq=>?_⟩
 · obtain ⟨i,rfl⟩:=(node Z' hK).surjective i; rw [hv,tag,tag]; exact he.footing i
 · obtain ⟨i,rfl⟩:=(node Z h).surjective i; rw [tag] at hi; obtain ⟨j,h₁,h₂⟩:=he.extend x i hi; exact ⟨(T₁ j),(hv j).trans (congr_arg _ h₁),(Z'.tag hK j).trans h₂⟩
 obtain ⟨i,rfl⟩:=(node Z' hK).surjective i; obtain ⟨j,rfl⟩:=(node Z' hK).surjective j; rw [hv,hv] at hi; rw [tag,tag] at heq; exact congr_arg _ (he.firm i j ((T).injective hi) heq)
include hP
lemma roll(h₀:4<f.val) : Ribbon.Drops (thread Z h) (thread Z' hK) hF M:= by
 have hu(i:Ty F k): root Z (τ i)=Φ (root Z' i):= ((nest Z Z' hF).footing i).symm; have hi(i:Ty F k): M (T₁ i)= T (τ i):= by unfold lower; rw [Equiv.symm_apply_apply]
 refine Ribbon.descents _ _ hF (project_nest ..) (fun i=>rfl) ?_ h₀ hP.symm ?_
 · intro i; obtain ⟨i,rfl⟩:=(T₁).surjective i; rw [hi]; change (R.activities.reg (map Z _)).support=Finset.image _ (R'.activities.reg (map Z' _)).support; rw [paid,paid,hP,hu]; unfold spine court; dsimp only; rw [← Finset.image_singleton]; exact Deck.ringed hF _ _
 intro i V he; obtain ⟨i,rfl⟩:=(T₁).surjective i; rw [hi]; rcases i with i|i; swap; · change R.activities.E (Z.slip _) _= R'.activities.E (Z'.slip _) _; rw [Z.quiet,Z'.quiet]; rfl
 change R.activities.E (X.model (Φ i)) _= R'.activities.E (X'.model i) _; rw [X.value,X'.value]; apply Eq.symm (X.off F f i (Φ i) ((L).links V) V ?_); rw [(L).expansion]; exact fun _ _ _=>rfl
-- The open indices are the complement of the addresses retained by the ribbon.
omit hP
lemma lamp : Drawing.Opens (thread Z h) (fun i=> i∉Set.range (map Z)):= ⟨fun _ h=>h,fun _ h hp=>False.elim (h hp)⟩
end Pad
end YM.Qlocal.Versal
