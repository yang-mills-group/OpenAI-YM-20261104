import YM.Contacts.Poetry.Setup
/-! Under compatible notebook for legacy. All covers; no price Sharp hull yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Poetry
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L : Side} {M m n j : ℕ} {K : Teller G}
variable {P:Patch}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
variable (Ξ:Lecturer R m) (Ξ':Lecturer R' m)
def ConcordP (q : F.val=f.val*M) (Ξ:Lecturer R m) (Ξ':Lecturer R' m) := ∀ (i:Site F) (U:Config G f), let l:= Macrame.normal (Deck.divides q) q; R'.activities.E (Ξ'.place i) (l.links U)= R.activities.E (Ξ.place (l.cut i)) U

def aisle (l:Lace h H M): Meter C F→ Meter c f:= Sum.map (verse_down l) l.high.cut
include hC he
lemma senate : Nest (Deck.divides hC) (aisle (L)) (lobby (Y)) (lobby (S)):= (nest_mint (Q:=Q) (hC:=hC) (he:=he) (H:=H) (h:=h)).sum (Deck.footing (h:=h) (H:=H) hC he)

lemma ledge (l k:ℕ) (i:Site F) (hh:f.val>4): regularFoot (decreed h) l k R (Ξ.place ((L).high.cut i))= (regularFoot (decreed H) l k R' (Ξ'.place i)).image ((L).low.cut) := by
  let Bz:= L; unfold regularFoot; rw [Ξ.support,Ξ'.support]; have hx: neighbors m (Bz.high.cut i)= (neighbors m i).image Bz.high.cut:= inclined (fineP h H hC) m i
  rw [enlargement,enlargement, hx,show inspected ((neighbors m i).image Bz.high.cut)= (inspected (neighbors m i)).image Bz.high.cut from voyages (fineP h H hC) hh _, image_image]
  let U:=(inspected (neighbors m i)).image (decreed H).parent
  rw [show ((inspected (neighbors m i)).image ((decreed h).parent ∘ Bz.high.cut)) = U.image Bz.low.cut from (by unfold U; rw [image_image]; apply image_congr; intro j _; exact Bz.position _)]
  exact ringed hC ..

lemma parallel (p:Meter C F) (n l:ℕ) (hp:R'.path=R.path) (ht:4 < f.val) : vote R'.path p=vote R.path (aisle (L) p) ∧ areas R T n l (topic (S) Ξ (aisle (L) p))=(areas R' T' n l (topic (Y) Ξ' p)).image (L).low.cut := by
  rcases p with p|p; · exact Stellar.voy (hC:=hC) (he:=he) (T:=T) (T':=T') p n l hp ht
  exact ⟨rfl,ledge Ξ Ξ' n l p ht⟩ -- orientation

variable {Ξ Ξ'}
variable (hr : R'.path= R.path) (hp : R'.p=R.p) (hf:R'.beta=R.beta) (hx: ConcordP (fineP h H hC) Ξ Ξ')
    -- post-comp ratio per ℓ
    (haw : 2*(generous 0 (radiusB p) m+3)<c.val)
    (a:ℝ) (z:Air f G) (O:ChartRatio G)
include hr hp hf hx haw A
omit hr in
lemma duet (i:Site F): X'.inhale R' a (X'.liftA R'.beta (blow (L) z)) (.inl (Ξ'.place i)) = X.inhale R a (X.liftA R.beta z) (.inl (Ξ.place ((L).high.cut i))) := by
  rw [hf,A.rolls]; let p' := Ξ'.place i; let p₀:=Ξ.place ((L).high.cut i); let w:= X.liftA R.beta z; let U:= X.input w; let f₀:=(L).high; let V:= f₀.links U; let i':= f₀.cut i
  have hH : 4<f.val := by have hs:= A.old.buys; have hm:= P.L.property; have hh:c.val≤ _:= h ▸ Nat.le_mul_of_pos_right _ hm; omega -- f shadow
  have ht: (L).high.cut=f₀.cut:=rfl
  have hX: R'.activities.regularOccurrence R'.p p' V=R.activities.regularOccurrence R.p p₀ U:= by
    unfold Activities.regularOccurrence p' p₀; rw [Ξ.support,Ξ'.support,show neighbors m (f₀.cut i)=(neighbors m i).image f₀.cut from inclined (fineP h H hC) m i,hp]
    have hh: Healthy R.p.threshold (neighbors m i) V↔ Healthy R.p.threshold ((neighbors m i).image f₀.cut) U:= Deck.vigor (fineP h H hC) U hH ..
    by_cases he: Healthy R.p.threshold (neighbors m i) V; · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (hh.1 he)]; exact hx i U
    rw [masked_ne _ _ _ _ he, masked_ne _ _ _ _ (hh.not.mp he)]
  unfold Coat.inhale; rw [(A.glassU w).2.2,A.D.1,A.D.2]
  refine congr_arg₂ _ (neg_inj.mpr hX) ?_ -- edit
  change _= X.enforce (2*a) w (X.plaza (regularFoot (decreed h) 0 B R (Ξ.place i'))); rw [show regularFoot (decreed h) _ _ _ _= _ from (ledge (hC:=hC) (he:=he) Ξ Ξ' 0 B i hH)]
  exact A.porter _ _ haw ((Y).ratio.parent i) (habitat Ξ' 0 B (lt_of_lt_of_le (by norm_num) A.old.sight.1) T' i).2 _ w

lemma casting (i:Meter C F) (hh:vote R'.path i≤ B) (Z :ℝ) (l:ℕ) (k k':Finset ℕ) : X'.vertex R' O Z a k l (blow (L) z) (topic (Y) Ξ' i)= X.vertex R O Z a k' l z (topic (S) Ξ (aisle (L) i)):= by
  rcases i with i|i; · exact A.granted hr hp hf a z O i hh Z l k k'
  exact congr_arg (fun t=>Real.exp t-1) (duet A hp hf hx haw a z i)
end YM.PhysicalNext.Repeat.Poetry
