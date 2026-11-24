import YM.RG01Estimate.Halliard
/-!
 # Genuine polynomial sources aligned prerevision. Composition Seal not optimized (eta bought separately).
 `Yard.preprints` and `Corridor.Advert` for RG02/03. Charges incurred *before declaring exact trial*.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Precise
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge Set
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural Macrame
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat Roost Boulevard Award
open Evoc Deck AbsoluteSums.Animals Board Promise Slide Trio Abacus
open Progress.DirectedRecipe Next.Scheduling
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{U:Alloy X D}(R:Factor U)
   {c f:Side}{N m d n i j r ℓ e :ℕ} {Y:Type} (β:ℝ) (H : f.val=c.val*(U.B.a.S.block m).val)
   (V : Insured U N m d H β Y)
local notation "J" => U.B.a.clock.J (m+1)
local notation "I" => U.B.a.clock.J m
local notation "P" => U.B.a.clock.adm (m+1)
local notation "L" => D.L (U.B.a.clock.J (m+1))
local notation "B" => U.B.a.budget m
local notation "B'" => U.B.a.budget (m+1)
local notation "χ" => Chi.canonical
local notation "γ" => U.B.kin.alpha N m
local notation "x" => U.B.a.clock.hatBeta m
local notation "𝕊" => Pane.panel U m H
local notation "T" => Pane.orchestra U N H
local notation "A₀" => X.O
local notation "X₀" => (R.target (U.B.a.clock.J (m+1)) (U.B.a.clock.J m))
local notation "ε" => gStep β
local notation "B''"=> Meadow.studio ℓ (radiusB x)
local notation "qt" => gStep β^(r+1)
local notation "P₀" => (Trio.fence ℓ (radiusB x))
local notation "n₀" => (Trio.tent ℓ (radiusB x))

section dawn
-- solar permissions. selected ports: don't expose projections in opaque Equality!
abbrev shape (U:Alloy X D)(m ℓ:ℕ) := Trio.fence ℓ (radiusB (U.B.a.clock.hatBeta m))
theorem shape_ack (U:Alloy X D)(m ℓ:ℕ) (i:Stars): (shape U m ℓ i).val=2*(Trio.tent ℓ (radiusB (U.B.a.clock.hatBeta m))+i.val):=rfl
abbrev starlet (U:Alloy X D)(m ℓ:ℕ) (i:Stars): ((Precise.shape U m ℓ i)*(U.B.a.S.block m)).val=(Precise.shape U m ℓ i).val*(U.B.a.S.block m).val:=rfl

-- post charges from Story budgets. Edifice of Query with F'. Internals no cal shift.
variable (u₀ : Precise.Horizon X D (U.B.a.clock.J (m+1)) (U.B.a.clock.J m) ℓ r n (U.B.a.clock.adm (m+1)))
    {s a b h :ℝ→ℝ}(F₀: Folio D (U.B.a.clock.adm (m+1)) u₀ e s a b h)
local notation "Ε" => u₀.Y (U.B.a.clock.hatBeta m)
local notation "fQ" => wick G L u₀.y x
local notation "k₀" => (Precise.sideFee D R.shape I J x + Precise.tiny G L x)
-- inputs imply Compatible P on apt Source-L **as given**, not π_r measures on U'. separate auth.
variable (W:Leads G c)
set_option quotPrecheck false
structure Herder (s a b h:ℝ→ℝ)(e:ℕ) where
    statusP : Abacus.Rack W.listing (Meadow.studio ℓ (radiusB (U.B.a.clock.hatBeta m))) W.pioneers
    real_h : Suggests (U.B.a.budget m) W (gStep β^(r+1)*h (U.B.a.clock.hatBeta m)) (Precise.tiny G (D.L (U.B.a.clock.J (m+1))) (U.B.a.clock.hatBeta m))
    turns : Trio.Mirrors statusP.polygon
    supply (i:Stars) : Insured U N m d (starlet U m ℓ i) β Y
    spans (i:Stars) : Board.Clockset H (starlet U m ℓ i) β V (supply i)
    splays (i j:Stars) : Board.Clockset (starlet U m ℓ i) (starlet U m ℓ j) β (supply i) (supply j)
    suits (i:Stars) : Leads G (Precise.shape U m ℓ i)
    likely (i:Stars): Suggests (U.B.a.budget m) (suits i) (gStep β^(r+1)*h (U.B.a.clock.hatBeta m)) (Precise.tiny G (D.L (U.B.a.clock.J (m+1))) (U.B.a.clock.hatBeta m))
    beams (i:Stars) : Abacus.Rack (suits i).listing (Meadow.studio ℓ (radiusB (U.B.a.clock.hatBeta m))) (suits i).pioneers
    graphs : Trio.CompatibleP (U.B.a.budget m) (Meadow.studio ℓ (radiusB (U.B.a.clock.hatBeta m))) statusP.polygon (fun i=> (beams i).polygon)
    precinct (i:Stars) : Narrative β (starlet U m ℓ i) (supply i) u₀ s a b (suits i).trunk e

-- closure of mirror without orientation cost; Cut hinges same centers.
lemma factors {c:Side}{G:Gauge} {X Y: Offer G c} (h:Trio.Mirrors X)(hz:Trio.Mirrors Y): Trio.Mirrors (X-Y):= fun o s i U=> congr_arg₂ (·-·) (h o s i U) (hz o s i U)
lemma mirror_list {G:Gauge}{c:Side}{Y:Stars→Side}{P₁ P₂:Offer G c}{W W':∀ i:Stars,Offer G (Y i)}{r:ℕ}(Q:BudgetPoint)
    (h: Trio.CompatibleP Q r P₁ W)(h':Trio.CompatibleP Q r P₂ W') : Trio.CompatibleP Q r (P₁-P₂) (W-W'):=
    ⟨fun i=> factors (h.moves i) (h'.moves i),fun i j c f V U hU ht hh=> congr_arg₂ (·-·) (h.pace i j c f V U hU ht hh) (h'.pace i j c f V U hU ht hh),
     fun i j c f V U hU ht => congr_arg₂ (·-·) (h.forks i j c f V U hU ht) (h'.forks i j c f V U hU ht), fun i V U hi=> congr_arg₂ (·-·) (h.visitL i V U hi) (h'.visitL i V U hi)⟩
variable (hA : OpenAt D R.shape (U.B.a.clock.adm (m+1)) u₀ F₀ (R.scout (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) (U.B.a.clock.hatBeta m))
    (ht : m < N)(he:β ∈ Shoot.band U.B.a (m+1))
    (UQ : ℕ→Finset Y)(hq:∀ i, ∀ᶠ k in atTop,i∈ UQ k)
    (A: Chartlet R.shape U N m H V.rep) (hF: SeekR R.shape U N m H A)
    (p' : Herder β H V u₀ W s a b h e)
    (hw : Routed.Allowed R) (hY:2≤r)(hR:r ≤ U.B.a.clock.J (m+1))(hm:1≤ n)
    (hp: s (U.B.a.clock.hatBeta m) ≥ 0)
local notation "hero" => (X₀).halo
include R p' hp hq hA ht he hF hw hY hR hm
set_option maxHeartbeats 500000 in
lemma sunrise (hn: house hero (radiusB x) d (Fate.steps r)+optic hero (radiusB x) d+5 ≤ B'')(hM : Meadow.studio hero (radiusB x)≤B'')(hν:4* B''+16 ≤ c.val) :
    ∀ᶠ k in atTop, ∃ f:∀ i:Stars, Award.Position (G:=G) (B) x Ε β γ fQ (Precise.shape U m ℓ i) L B'' (r+1),
        Trio.CompatibleP (B) (B'') (Evoc.aspect A V.music (Fate.steps r) χ γ (UQ k) k - p'.statusP.polygon) (fun i=> (f i).pact.polygon) ∧
       ∀ i, (f i).q' ≤ qt * Precise.pot h x ∧ (f i).e'≤ k₀ ∧ (f i).y'≤F₀.mist x ∧ (f i).μ ≤ ε^((r+1)+2)*b x∧(f i).V = capΨ D P u₀ a x:= by
    have hz:=starlet U m ℓ
    let V₁ i:= p'.supply i
    choose U' hS using fun i:Stars => Board.authorizes R (starlet U m ℓ i) (V₁ i|>.rep) (Trio.highChair ℓ _ i|>.2) (by rw [(V₁ i).β']; exact he) (V₁ i).pathU (V₁ i).clip (V₁ i).point (V₁ i).legal ht
    have hh : house (X₀).halo (radiusB x) d (Fate.steps r) ≤ B'':= by omega
    have hp' (i:Stars) := Precise.talent R _ _ (V₁ i) u₀ F₀ hA ht he UQ hq (U' i) (hS i) (p'.suits i) (p'.likely i) (p'.beams i) (p'.precinct i) hw hY hR hm (Trio.taller ..) (Trio.highChair ℓ _ i|>.2) hp hh hM
    filter_upwards [eventually_all.mpr hp'] with k hk
    choose f hf hg ht' hu hv hs using hk
    let Z i:= (f i).pact.polygon
    let H' i:= Evoc.aspect (U' i) ((V₁ i).music) (Fate.steps r) χ γ (UQ k) k
    let M' := Evoc.aspect A V.music (Fate.steps r) χ γ (UQ k) k
    have hH : Trio.CompatibleP B B'' M' H':= by
       have hC i:=Trio.highChair ℓ (radiusB (U.B.a.clock.hatBeta m)) i|>.1
       refine ⟨fun i=>Evoc.reflections _ _ _ _ _ _ _,fun i j=>?_ ,fun i=>?_ ,fun i=>?_ ⟩
       · exact Board.coverUp R ht _ _ β _ _ r _ _ _ (B'') hn hM (hC i) (hC j) (p'.splays i j) he k -- param order check
       · -- spans provides K other orientation. need swap lemma or take Compatible symmetric
         intro y z U' V' hv hu hZ ; symm; apply Board.coverUp R ht H _ β V A r _ _ _ (B'') hn hM hν (hC i) (p'.spans i) he k z y V' U' hu hv; exact fun i hi hj=> (hZ i hi hj).symm
       exact (Board.morals R ht H β V A hF r (UQ k) (B'') k hh hM i).sites
    have hp' : Z= H'-(fun i=> (p'.beams i).polygon):= funext hf
    refine ⟨f, ?_, fun i=> ⟨hg i,ht' i,hu i,hv i,hs i⟩⟩
    change Trio.CompatibleP (B) (B'') _ Z; rw [hp']; exact mirror_list B hH p'.graphs
end dawn
end YM.RG01Estimate.Precise
