import YM.AllOrder.Burn.Stereo
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Repeat.Deck Repeat.Deck.Mint Till Greenbelt 
open Poll Pond MeasureTheory ProbabilityTheory Stellar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} (hC : C.val=c.val*M) (he:2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "Y" => stepped Q H
local notation "Y'" => stepped Q h
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
include hC he
open Deck Mint Till SectorMeasure Oriented
variable (V : Locale G) (s:Seed R V)(s':Seed R' V)(hq: R'.p=R.p)
include s s' hq
-- width check needed for enforcing.Acoustic.Current. explicit post.
abbrev plode (L': Lace h H M) : Mandala C F → Mandala c f:= Sum.map (verse_down L') L'.high.cut
def wrapper (L': Lace h H M) (u:Yard C F): Yard c f:= u.image (plode L')
lemma reg_scape (m v:ℕ)(i:Site F)(hp:f.val>4): Raw.regularFoot (decreed h) m v R (s.model ((L).high.cut i))=(Raw.regularFoot (decreed H) m v R' (s'.model i)).image (L).low.cut := by
 unfold Raw.regularFoot; rw [(s.reg _).1,(s'.reg i).1,hq]; let Tz:= L; have hx : court (Tz.high.cut i) R.p.B=(court i R.p.B).image Tz.high.cut:= by rw [court, court, ← Finset.image_singleton]; exact Deck.ringed (fineP h H hC) _ _
 rw [enlargement,enlargement,hx,show inspected ((court i R.p.B).image Tz.high.cut)=(inspected (court i R.p.B)).image Tz.high.cut from voyages (fineP h H hC) hp _, Finset.image_image]; let S := (inspected (court i R.p.B)).image (decreed H).parent; rw [show ((inspected (court i R.p.B)).image ((decreed h).parent ∘ Tz.high.cut))= S.image Tz.low.cut from (by unfold S; rw [image_image]; apply image_congr; intro j _; exact Tz.position _)]; exact Deck.ringed hC _ _
variable (A : Deck.Stellar hC he K p X X')(hr : R'.path= R.path) (hf:R'.beta=R.beta) {z : Air f G} {a:ℝ}{O:ChartRatio G}
include A hf
lemma maskedOff (y: Site F)(hu :Config G f): R'.activities.regularOccurrence R'.p (s'.model y) ((L).high.links hu) = R.activities.regularOccurrence R.p (s.model ((L).high.cut y)) hu:= by
 have he' : 4<f.val := by have hs:= A.old.buys; have hm := P.L.property; have hh:c.val≤ f.val:= h ▸ Nat.le_mul_of_pos_right _ hm; omega
 let D':=L; let z:=D'.high.cut; have hx : court (z y) R.p.B=(court y R.p.B).image z := by rw [court,court,← Finset.image_singleton]; exact Deck.ringed (fineP h H hC) _ _
 let M:= R.p.threshold; let m:Site f:= (L).high.cut y
 let a:=(L).high.links hu; unfold Activities.regularOccurrence; rw [(s.reg _).1,(s'.reg _).1,s.value,s'.value,hq,hx];
 by_cases hA:Healthy M (court y R.p.B) a; · rw [masked_eq _ _ _ _ hA,masked_eq _ _ _ _ (show Healthy R.p.threshold ((court y R.p.B).image z) hu from (Deck.vigor (fineP h H hC) hu he' ..).1 hA)]; refine s.off F f y m a hu ?_; rw [show expandAt y a=expandAt m hu from (L).high.expansion ..]; exact fun _ _ _=>rfl
 rw [masked_ne _ _ _ _ hA,masked_ne _ _ _ _ (show ¬Healthy R.p.threshold ((court y R.p.B).image z) hu from (Deck.vigor (fineP h H hC) hu he' ..).not.mp hA)]
variable (hu:R.p.B≤2*radiusB p)
include hr hu
lemma grantedT (i:Mandala C F) (hh:ageV R'.path i≤ B) (Z :ℝ) (l:ℕ) (k k':Finset ℕ) : X'.vertex R' O Z a k l (blow (L) z) (spin (Y) s'.model i)= X.vertex R O Z a k' l z (spin (stepped Q h) s.model (plode (L) i)):= by
 rcases i with i|i; · exact A.granted hr hq hf a z O i hh ..
 apply congr_arg (fun v=> Real.exp v-1) (show X'.farLog R' a O (blow L z) (scratch s'.model (Sum.inr i))= X.farLog R a O z (scratch s.model (plode (L) (Sum.inr i))) from ?_)
 unfold farLog; rw [hf,A.rolls];
 unfold scratch plode inhale Raw.expo Raw.space; dsimp only [Sum.elim, Sum.map_inr]; rw [(A.glassU ..).2.2, A.D.1, A.D.2, maskedOff hC he V s s' hq A hf i]; -- projection of enforce
 apply congr_arg; have hM:=A.old.buys; have hs:= A.old.sight; let v:= Raw.regularFoot (decreed H) 0 B R' (s'.model i); let n:= Mint.width 0 B (2*B)
 have hπ : f.val>4 := by have hQ:c.val≤ f.val:= h ▸ Nat.le_mul_of_pos_right _ P.L.property; omega
 rw [ (show Raw.regularFoot (stepped Q h).ratio 0 B R (s.model ((L).high.cut i))=v.image (L).low.cut from reg_scape hC he V s s' hq _ _ i hπ)]; apply A.porter v n (by unfold n Mint.width; omega) ((decreed H).parent i); -- finance 0
 intro x hx; unfold v Raw.regularFoot at hx; rw [(s'.reg i).1,hq] at hx; obtain ⟨z,hz,ht⟩:=halo_spec.mp (inspected_price (decreed H) 0 B (court i R.p.B) (by omega) hx); obtain ⟨p,hp,rfl⟩:= mem_image.mp hz; have hv:separation ((decreed H).parent i) ((decreed H).parent p)≤R.p.B+1:= (Work.E04.parent_separation ..).trans (Nat.add_le_add_right (by simpa only [halo_spec,mem_singleton,exists_eq_left] using hp) _); exact (neighbors_mem ..).2 ((separation_triangle _ ((decreed H).parent p) _).trans (by unfold n Mint.width; omega))
end YM.AllOrder.Burn
