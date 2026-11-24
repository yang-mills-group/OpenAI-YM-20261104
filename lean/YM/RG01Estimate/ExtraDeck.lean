import YM.RG01Estimate.ExtraVoice
/-! # transfer Terms in caps, exact even before derivative audits. Requires cross-period faithful E stencils. No global K comparison, no equality of the resulting log analytic sums yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext.Repeat Deck Mint Greenbelt
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Γ : Type} {G : Gauge} {c f C F L'':Side} {P : Patch} {M D' p : ℕ} {K : Teller G}
section deck
variable {h : f.val=c.val*P.L.val} {H:F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M}{hc:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC hc
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {R:RG.Rep G f}{R':RG.Rep G F} {V: Lex Γ f} {V': Lex Γ F}
def ringD (A:Lace h H M) : Site F×Γ → Site f × Γ:= Prod.map A.high.cut id
def warps (A:Lace h H M) : Header Γ C F → Header Γ c f:= Sum.map (ringD A) (verse_down A)

-- ALL short E* entries. Preserve identical on periodic components of all gauges/lifts; no long E.
structure Charts (hC : C.val=c.val*M)(hc:2≤c.val)(R:RG.Rep G f)(R':RG.Rep G F)(V:Lex Γ f)(V': Lex Γ F): Prop where
    -- only projection; exact along kernels under matched real β/path.
    returns (i) : (R.activities.reg (V (ringD (Lace.project (h:=h) (H:=H) hC hc) i))).support=(R'.activities.reg (V' i)).support.image (Lace.project (h:=h) (H:=H) hC hc).high.cut
    mills (i) (A: Config G f): R'.activities.E (V' i) ((Lace.project (h:=h) (H:=H) hC hc).high.links A)=R.activities.E (V (ringD (Lace.project (h:=h) (H:=H) hC hc) i)) A

variable {m b:ℕ} {T:Tube G (stepped Q h)}{T':Tube G (stepped Q H)}
      (A: Charts (h:=h) (H:=H) hC hc R R' V V') (hf:R'.path=R.path)(hq:R'.p=R.p)
      (ht:4 < f.val)

include A ht
lemma aspirates (m b:ℕ)(i : Site F × Γ):
   regularFoot (decreed h) m b R (V (ringD (L) i))= (regularFoot (decreed H) m b R' (V' i)).image (L).low.cut := by
   let X:=(R'.activities.reg (V' i)).support
   unfold regularFoot enlargement; rw [A.returns]; change halo _ ((inspected (X.image (L).high.cut)).image _)=(halo _ ((inspected X).image _)).image _
   rw [show RG.inspected (X.image (L).high.cut)=_ from voyages (fineP h H hC) ht X]
   let U:=(inspected X).image (decreed H).parent; rw [show (halo (m*b) U).image (L).low.cut=halo (m*b) (U.image (L).low.cut) from (ringed hC U (m*b)).symm]; apply congr_arg; unfold U
   rw [Finset.image_image, Finset.image_image]; exact Finset.image_congr fun _ _=> (L).position _

include hf
lemma sails (T:Tube G (stepped Q h))(T':Tube G (stepped Q H)) (i : Header Γ C F) : fit R'.path i= fit R.path (warps (L) i) ∧ areas R T m b (mint (S) V (warps (L) i))=(areas R' T' m b (mint (Y) V' i)).image (L).low.cut:= by
   rcases i with i|i; · exact ⟨rfl,aspirates A ht m b i⟩
   exact Stellar.voy (T:=T) (T':=T') _ m b hf ht
omit ht hf A
include hC hc in
lemma sailing (h': KernelChoices) : Nest (Deck.divides hC) (warps (L)) (aisle (Γ:=Γ) (stepped h' H)) (aisle (stepped h' h)):= (Deck.footing (h:=h) (H:=H) hC hc|>.pr).sum (Stellar.nest_mint ..) -- Type?

variable {E :Forest (stepped Q h).ratio}{E':Forest (stepped Q H).ratio}
     {X:Coat T E} {X' : Coat T' E'} {β s : ℝ}(he : Stellar hC hc K s X X')
     (hs : R'.beta=R.beta) (B: ChartRatio G)
local notation "D" => radiusB s
include he A hq hf hs
lemma loops_with {w :ℕ}(i:Header Γ C F)(hz: fit R'.path i≤ radiusB s)(t a:ℝ)(z:Air f G) (l:ℕ)
     (hu: ∀ i, regularFoot (decreed H) 0 (radiusB s) R' (V' i)⊆neighbors w ((decreed H).parent i.1)) (hζ:2*(w+3)< c.val)
     (Yk W':Finset ℕ) : X'.vertex R' B t a W' l (blow (L) z) (mint (Y) V' i)=X.vertex R B t a Yk l z (mint (S) V (warps (L) i)):= by
   rcases i with i|i
   swap; · exact he.granted hf hq hs a z B i hz t l _ _
   have hT : 4<f.val:=by have hq:= he.old.buys; have hp:c.val≤f.val:= h ▸ Nat.le_mul_of_pos_right _ P.L.property; omega
   let A':= V'; let K:= ‹Lex Γ f›; let j:= K (ringD (L) i); let J:= A' i
   apply congr_arg (fun v=> Real.exp v-1)
       (show X'.farLog R' a B (blow (L) z) (.inl (.inl J))=X.farLog R a B z (.inl (.inl j)) from ?_)
   let v:=X.liftA R.beta z; let W:= X.input v
   unfold farLog; rw [hs, he.rolls]; change X'.inhale R' a _ (.inl J)=X.inhale _ _ _ (.inl j)
   have hf_ : R'.activities.regularOccurrence R'.p J ((L).high.links W)=R.activities.regularOccurrence R.p j W:= by
       unfold Activities.regularOccurrence; rw [hq]
       let Y₁:=(R'.activities.reg J).support; let t:=R.p.threshold
       have hp : (R.activities.reg j).support= Y₁.image (L).high.cut:= A.returns i
       have hv : Healthy t Y₁ ((L).high.links W) ↔ Healthy t (Y₁.image (L).high.cut) W:= vigor (fineP h H hC) W hT ..
       rw [hp]; by_cases hQ : Healthy t Y₁ ((L).high.links W)
       · rw [masked_eq _ _ _ _ hQ,masked_eq _ _ _ _ (hv.1 hQ)]; exact A.mills i W
       rw [masked_ne _ _ _ _ hQ,masked_ne _ _ _ _ (hv.not.mp hQ)]
   let Z:=regularFoot (decreed H) 0 D R' J
   unfold Coat.inhale; rw [he.D.1,he.D.2]
   change -(R'.activities.regularOccurrence _ _ (X'.input _))* X'.enforce (2*a) _ (X'.plaza Z)=-(R.activities.regularOccurrence _ _ W)*_
   rw [(he.glassU v).2.2, hf_, he.porter Z w hζ _ (hu i)]; exact congr_arg₂ _ rfl (congr_arg (fun q=>X.enforce (2*a) v (X.plaza q)) (aspirates A hT _ D i).symm)
end deck
end YM.RG01Estimate.Evoc
