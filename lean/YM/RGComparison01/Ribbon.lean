import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Optic
/-!
 # Alphabet for short E stencil re-entry

 Keep all mask identities. Transferrable packets from SAME input model
 on compatible periods; not discarding its rough tail. No chart/Cash
 premises when stating E correspondence. `Ribbon` not requested on E remainders. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F : Side} {P : Patch} {M n r : ℕ} {K : Teller G}

/-- Chosen (short) E terms. `ride` indexes multiplicity truncations
 AFTER estimating their actual l¹ bill. Can take path index here. -/
structure Ribbon {f : Side} (R : RG.Rep G f) (n : ℕ) where
  keep : ℕ → Prop
  ride : {i : ℕ // keep i} → ℕ
  finite (j:ℕ) : {i : {i : ℕ // keep i} | ride i ≤ j}.Finite
  radius i (hi : keep i) : (R.activities.reg i).support ⊆ neighbors n (R.activities.reg i).site

variable {R : RG.Rep G f} {R' : RG.Rep G F}
namespace Ribbon
abbrev Node (κ : Ribbon R n) := {i : ℕ // κ.keep i}
abbrev home (κ : Ribbon R n) (i : Node κ) := (R.activities.reg i.val).site
def empty (R : RG.Rep G f) (n : ℕ) : Ribbon R n :=
  ⟨fun _=>False,fun i=>i.property.elim,fun _=> Set.finite_empty.subset (fun k _ => k.property.elim),fun _ hk=> hk.elim⟩

variable (κ:Ribbon R n) (Φ:Ribbon R' n) (p:Ratio c f)
lemma covers (z l : ℕ) (hp:0<l) (t:Node κ) :
    p.parent (κ.home t) ∈ regularFoot p z l R t.val ∧ regularFoot p z l R t.val ⊆ neighbors (Mint.width z l n) (p.parent (κ.home t)) := by
  let X:= (R.activities.reg t.val).support; let x:=κ.home t
  refine ⟨?_,fun i hi=>?_⟩
  · apply halo_subset; apply mem_image_of_mem; exact mem_union_left _ (R.activities.reg t.val).anchor
  obtain ⟨w,hw,hz⟩:= halo_spec.mp (inspected_price p z l X hp hi); obtain ⟨w,hk,rfl⟩:=mem_image.mp hw
  have he: separation (p.parent x) (p.parent w) ≤ n+1:= (Work.E04.parent_separation ..).trans (add_le_add ((neighbors_mem ..).1 (κ.radius t.val t.property hk)) le_rfl)
  apply (neighbors_mem ..).2; apply (separation_triangle _ (p.parent w) _).trans
  change separation (p.parent x) (p.parent w) + separation (p.parent w) i ≤ _; unfold Mint.width; nlinarith only [he,hz,hp]

variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices}
section drop
variable (hF : F.val=f.val*M)
local notation "L" => normal (Deck.divides hF) hF
structure Drops (K : Φ.Node → κ.Node) : Prop where
  step : Nest (Deck.divides hF) K Φ.home κ.home
  size i : Φ.ride i = κ.ride (K i)
  view i : (R.activities.reg (K i).val).support = ((R'.activities.reg i.val).support).image ((normal (Deck.divides hF) hF).cut)
  turn i (V : Config G f) : R.activities.regularOccurrence R.p (K i).val V = R'.activities.regularOccurrence R'.p i.val ((L).links V)

lemma descents {K : Φ.Node → κ.Node} (ht : Nest (Deck.divides hF) K Φ.home κ.home) (hp: ∀ i, Φ.ride i=κ.ride (K i))
    (he : ∀ i, (R.activities.reg (K i).val).support = ((R'.activities.reg i.val).support).image ((L).cut)) (hh:f.val>4) (hR:R.p=R'.p)
    (hf : ∀ i (V : Config G f), Healthy R.p.threshold (R.activities.reg (K i).val).support V → R.activities.E (K i).val V=R'.activities.E i.val ((L).links V)) : Drops κ Φ hF K := by
  refine ⟨ht,hp,he,fun i V=>?_⟩; let S:= (R'.activities.reg i.val).support
  have hB : Healthy R'.p.threshold S ((L).links V) ↔ Healthy R.p.threshold (R.activities.reg (K i).val).support V:= by rw [he,hR]; exact Deck.vigor hF V hh _ _
  unfold Activities.regularOccurrence; by_cases hx:Healthy R'.p.threshold S ((L).links V)
  · rw [masked_eq _ _ _ _ hx,masked_eq _ _ _ _ (hB.mp hx)]; exact hf i V (hB.mp hx)
  rw [masked_ne _ _ _ _ hx,masked_ne _ _ _ _ (mt hB.mpr hx)]
def drop_void (R : RG.Rep G f) (R' : RG.Rep G F) (n : ℕ) (x : (Ribbon.empty R' n).Node) : (Ribbon.empty R n).Node:=x.property.elim
lemma emptyDrops (R : RG.Rep G f) (R' : RG.Rep G F) (n : ℕ) : Drops (Ribbon.empty R n) (Ribbon.empty R' n) hF (Ribbon.drop_void R R' n) :=
    ⟨⟨fun i=> i.property.elim,fun _ i _=> i.property.elim,fun i _ _ _=> i.property.elim⟩, fun i=>i.property.elim, fun i=>i.property.elim,fun i _=>i.property.elim⟩
end drop
section life
variable (hC:C.val=c.val*M) (he : 2≤ c.val) {Z : Φ.Node→κ.Node}
variable (Y : Drops κ Φ (Deck.fineP h H hC) Z)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y'" => stepped Q H
include Y he

lemma descentZ (u l : ℕ) (i : Node Φ) (hh:4<f.val) :
    regularFoot (decreed h) u l R (Z i).val=(regularFoot (decreed H) u l R' i.val).image ((L).low.cut) := by
  let p:= (R'.activities.reg i.val).support; let L':= L
  rw [regularFoot,regularFoot,Y.view]
  have hx: inspected (p.image L'.high.cut)= (inspected p).image L'.high.cut:= Deck.voyages (Deck.fineP h H hC) hh _
  change enlargement (decreed h) u l (inspected (p.image L'.high.cut))=_
  rw [hx,enlargement,enlargement, image_image]
  rw [show ((inspected p).image ((decreed h).parent ∘ L'.high.cut)) = ((inspected p).image (decreed H).parent).image L'.low.cut from by
    rw [image_image]; apply image_congr; intro j _; exact L'.position j]
  exact Deck.ringed hC _ _

lemma pouring : Nest (Deck.divides hC) Z ((decreed H).parent ∘ Φ.home) ((decreed h).parent ∘ κ.home) := by
  let A := Deck.footing (h:=h) (H:=H) hC he; have ha := A
  have hV := Y.step
  refine ⟨fun i=>?_,fun x i hx=>?_,fun i j hi hh=>?_⟩
  · have hu := ha.footing (Φ.home i); change _=(decreed h).parent _; exact hu.trans (congr_arg (decreed h).parent (hV.footing i))
  · obtain ⟨j,hz,hJ⟩:= ha.extend x (κ.home i) hx; obtain ⟨k,hp,hK⟩:= hV.extend j i hz.symm
    exact ⟨k,hp, (congr_arg (decreed H).parent hK).trans hJ⟩
  have hz := (hV.footing i).trans ((congr_arg κ.home hi).trans (hV.footing j).symm)
  exact hV.firm i j hi (ha.firm _ _ hz hh)

variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X')
local notation "B" => radiusB p
include A
lemma Vertex (hb:R'.beta=R.beta) (i:Φ.Node) (hk:2*(Mint.width 0 B n+3)<c.val)
    (a W : ℝ) (z : Air f G) (O:ChartRatio G) (k k':Finset ℕ) (l:ℕ) :
    X'.vertex R' O W a k l (Stellar.blow (L) z) (Opacity.key (Y') i.val)= X.vertex R O W a k' l z (Opacity.key (S) (Z i).val) := by
  have he : 4<f.val := by have hs:= A.old.buys; have hm := P.L.property; have hh:c.val≤ f.val:= h ▸ Nat.le_mul_of_pos_right _ hm; omega
  let u:=X.liftA R.beta z
  have hP:= (Φ.covers (decreed H) 0 B (lt_of_lt_of_le (by norm_num) A.old.sight.1) i).2
  have hv:= A.porter _ (Mint.width 0 B n) hk ((decreed H).parent (Φ.home i)) hP (2*a) u
  have hF := descentZ (h:=h) (H:=H) κ Φ hC (by assumption) Y 0 B i he
  change Real.exp (X'.farLog R' a O (Stellar.blow (L) z) (.inl (.inl i.val)))-1=_
  apply congr_arg (fun p=> Real.exp p-1) ?_
  unfold Coat.farLog Coat.inhale Raw.expo Raw.space
  dsimp only [Sum.elim]
  rw [hb,A.rolls,A.D.1,A.D.2]; -- legacy input
  change regularFoot (S).ratio 0 B R (Z i).val=_ at hF
  rw [hF, (A.glassU (X.liftA R.beta z)).2.2]; exact congr_arg₂ _ (congr_arg Neg.neg ((Y.turn i (X.input u)).symm)) hv
end life
end Ribbon
end YM.RGComparison01
