import YM.LocalTaylorR2.Capstone.Freighter
/-!
 # At any Spring, any legal point. Install corrected E Taylor through the WHOLE reclosure.
    Two types of kept beams: common Mast furnishing and per-side calibration Omega stars within Rain.
    No choice of Representatives substituting unrelated recipes. Bound in THE invoice consumed
    by Spring.owns. Hard and Packets remain copied from actual (separate precision quote).
    In particular not trying to mutate its output K cells by changing lives/clip.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Capstone
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- include useful grade-specific setup (coreHere.error). expansion basis convention sprig.
open CalendarStep
local notation "❖" => Chi.canonical
section slate
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
variable (b:BudgetPoint) (X:Match.Alliance I H 1 0) (v:ℝ) (p:ℕ) (φ:Bool) (n:ℕ)
abbrev sheaves:= cohort H («χ»:=❖) X v (M:=p) (Candle.sprig H ❖) φ (fun i=>if φ then ¬ p+1 ≤ i else p+1 ≤ i)
def songKeep : Collection.Source G c:= { plusone I X ❖ v with
  logRead:=fun i=> if (pennant I i).2∈ Meadow.bouquet I n then 0 else (sheaves H X v p φ).logRead i }
-- uniform exp hit after dropping rows. Nonarchitectural h Ξ
lemma mosaic (u:ℝ) (h:Meadow.Budget b (Beam.marquee I b).reg (sheaves H X v p φ).logRead u):
    Meadow.Budget b (Beam.marquee I b).reg (songKeep H X v p φ n).logRead u:=by
  obtain ⟨k,hv,h⟩:=h; refine ⟨k,hv,?_⟩; intro i; simp only [songKeep]; split
  next _ => exact ⟨CouplingShape.reg_const _, sup_le (no_cost ..) (h i).2.1⟩
  exact h i
lemma terraform (hp: (plusone I X ❖ v).logRead=(sheaves H X v p true).logRead+(sheaves H X v p false).logRead):
    (Meadow.timbres X (χ:=❖) v n).logRead=(songKeep H X v p true n).logRead+(songKeep H X v p false n).logRead:=by
  funext i; rw [Pi.add_apply,Meadow.compass,hp]; simp only [songKeep]; split
  next=> rw [add_zero]
  rfl
lemma brave (σ:Signed)(p':Site c): Nonempty (((Beam.marquee I b).read (songKeep H X v p φ n)).Moves σ p'):=by
  -- choir selects per unturned index
  let k : ℕ → Config G c→ℝ:= (songKeep H X v p φ n).logRead
  have h (f:Magazine I→ Config G c→ℝ) (hx:(sheaves H X v p φ).logRead=choir f ∘ pennant I):
    k=choir (fun i=> if i∈ Meadow.bouquet I n then 0 else f i) ∘ pennant I:= by
    funext i; simp only [k,songKeep]; rw [hx]; unfold choir; split
    next h=> ext; simp [h]
    next h=> simp only [Function.comp_apply]; rw [if_neg h]
  unfold Listing.read; rw [show (songKeep H X v p φ n).logRead=_ from h _ rfl]
  exact Beam.moves I b ❖ X σ p' _
lemma layout_add {X Y Z: Collection.Source G c} (F U V t :Trio.Offer G c)(hu:F=U+V)(hv:X.logRead=Y.logRead+Z.logRead): (Marlin.bison X F t).regular=(Marlin.bison Y U t).regular+(Marlin.bison Z V t).regular:=by
  unfold Marlin.bison; rw [hu,hv]; funext i; rcases h : leanU c i with j|j <;> simp [Function.comp_apply,h,choir]
  ext x; simp [mul_add]
end slate
open Rain Roost Mallow
variable {G:Gauge} {M:Metals G} {D:Rolls M.p} {A:Alloy M D} (R:Factor A) {hm' : G.Simple} {l k: ℝ} {m n N:ℕ} {Q:In A.B.a m n} (H:Spring R N m n l k Q) (x:ℝ) (hx:x∈Icc l k) (p:ℕ) (φ:Bool) (hp:Mallow.RG12.Earned (ticketD G) R.shape A.delay)
local notation "y"=> A.B.a.clock.hatBeta m
local notation "y₁"=> A.B.a.clock.hatBeta (m+1)
local notation "z"=> Trio.base (Rain.lint R.target A m) (radiusB y)
local notation "k₀"=> Rain.lint R.target A m
local notation "j₁"=> A.B.a.clock.J (m+1)
local notation "j₀"=> A.B.a.clock.J m
local notation "Z"=> A.B.a.S.side m n
local notation "B" => A.B.a.budget m
local notation "v"=> A.B.kin.alpha N m
local notation "P"=> (H.H.latch x)
local notation "d"=> H.ordinal
local notation "U"=> H.H
local notation "u"=> Rain.noteX H.H H.knows x
local notation "T"=> H.W
set_option quotPrecheck false
local notation "Omo"=> (Rain.moor R.target A m)
local notation "J"=> Rain.screens R.target A m
local notation "Φ"=> H.V'
local notation "κ"=> (Φ) x
def tAffordable (i:Stars) :=
    let Y:=H.W.tiers i (u)
    stepsAt Y B (sheaves Y (show Match.Alliance Y Y 1 0 from Match.staple rfl rfl rfl) v p φ) d
abbrev grate : ∀ i:Stars,Trio.Offer G (Omo i):= tAffordable R H x p φ
abbrev rescue := Trio.ornament (J) (grate R H x p φ) (c:=Z)
def rigging := songKeep (H.H.houses (P)) (H.H.sister (P)) v p φ d
def sketch : Collection.Source G Z:= { (κ) with
   logRead:= (Marlin.bison (rigging R H x p φ) (rescue R H x p φ) (Rain.lights H.H H.knows H.W H.ordinal x)).regular }
-- Now ALL K from κ; including contributors from exact Ω p$t after regroup
variable (hY : p ≤ A.B.a.clock.J (m+1)) (hm:m<N)
local notation "a"=> Capstone.fare k₀ (A.B.a.params m) y
local notation "s"=> CalendarStep.loss j₁
local notation "o"=> (y₁^(requested (p+1) s))
include hp hY hm
lemma songs : Meadow.Budget B H.H.doors.reg (rigging R H x p false).logRead o ∧ (Rain.uptick H.H d x).logRead=(rigging R H x p true).logRead+(rigging R H x p false).logRead:=by
  obtain ⟨C,e,f,g,y₀,l₁,l',r,B',q,v₀,k',a₁,θ,i,N',he⟩:= engaged R ((A.B.a.S.oneStep m n).exact_size) (H.H.houses (P)) hm hp p hY s le_rfl -- n implicit?
  let h:= he.probed
  have hz:=allocation R ((A.B.a.S.oneStep m n).exact_size) (H.H.houses (P)) he (H.H.sister (P)) (le_refl (p+1)) (fun i=> p+1 ≤ i) (fun _ hi=>hi)
  constructor
  · apply mosaic; simpa only [sheaves,Bool.false_eq_true,ite_false] using! hz
  apply terraform; simpa only [sheaves,Bool.false_eq_true,ite_false,ite_true] using! YM.LocalTaylorR2.subtract (H.H.houses (P)) h (H.H.sister (P)) (v) (fun i=>p+1 ≤ i)
local notation "Z₀"=> (grate R H x p false)
local notation "P₀"=> (Rain.beacons H.H H.knows H.W (d) x)
local notation "Ω"=> (fun i:Stars=>2*(Fintype.card (Site (Omo i)):ℝ)*o)
lemma ceremonies : H.W.offers (d) (u)=grate R H x p true+grate R H x p false ∧ ∀ i:Stars,(∀ j,(B).Regular univ (Z₀ i j)) ∧ ∀ (W:Config G (Omo i)), flags (B).threshold W=∅ → ∀ l:List (Directions G (Omo i)), l.length≤(B).order → (∀ h∈l,‖h‖≤(B).threshold) → ‖leftDerivs (Boulevard.stillA (Trio.froth (Z₀ i))) l W‖ ≤ Ω i:=by
  let Y (i:Stars) := H.W.tiers i (u)
  let v' (i:Stars): Match.Alliance (Y i) (Y i) 1 0:=Match.staple rfl rfl rfl
  let A' (i:Stars):= sheaves (Y i) (v' i) v p
  have h (i:Stars) : ((T).offers (d) (u) i)=grate R H x p true i+grate R H x p false i ∧ Meadow.Budget B (Beam.marquee (Y i) B).reg (A' i false|>.logRead) o:=by
    obtain ⟨C,e,f,g,y₀,l₁,l',r,B',q,v₀,k',a₁,θ,j,N',he⟩:= engaged R (Rain.panes R.target A m i) (H.W.tiers i (u)) hm hp p hY (s) le_rfl
    constructor
    · rw [show (T).offers (d) (u) i=Meadow.barony (Y i) ❖ (d) (v) from rfl, terms_bloom (Y i) B (v' i) rfl rfl rfl]
      exact terms_chain (Y i) B d (by simpa only [sheaves,Bool.false_eq_true,ite_false,ite_true] using! YM.LocalTaylorR2.subtract (Y i) he.probed (v' i) (v) (fun i'=> p+1 ≤ i'))
    have hz:= allocation R (Rain.panes R.target A m i) (Y i) he (v' i) (le_refl (p+1)) (fun i'=> p+1 ≤ i') (fun _ hi=>hi)
    simpa only [A',sheaves,Bool.false_eq_true,ite_false] using! hz
  exact ⟨funext (fun i=> (h i).1), fun i=> ⟨watch (Y i) B (A' i false) (h i).2 d,fun j h' l h₁ h₂=> rails (Y i) B (A' i false) (h i).2 d j h' l h₁ h₂⟩⟩

lemma beaming : let U':=rescue R H x p false; let f:=oroW B z Ω
    P₀=rescue R H x p true+U' ∧ Meadow.Budget B (Marlin.leap z) U' (f*Real.exp (preExponent B*coverTicket k₀)) := by
  intro X' f
  obtain ⟨hf,hp⟩:= ceremonies R H x p hp hY hm
  have he:0≤o:=Real.rpow_nonneg (zero_le_one.trans (A.B.a.fits.delayed _).le) _
  have hK (i:Site Z):= Capstone.pace B J z Z₀ (fun j=> (hp j).1) (q:=Ω) (fun i=> by positivity) (by unfold Trio.base; omega) i (fun j=> (hp j).2)
  have hv : 0≤f:= (hK 0).2.1
  refine ⟨funext (fun (i:Site Z)=> Capstone.offers_add J ((T).offers (d) (u)) i _ _ hf),fun i=>f,fun i=>?_,fun i=> hK i⟩ -- tuple
  apply budget_finite
  · intro i; split; exact mul_nonneg hv (Real.exp_pos _).le; rfl
  rw [Finset.sum_eq_single i]; rw [if_pos (show (leap z i).site=i from rfl)]
  · apply mul_le_mul_of_nonneg_left _ hv; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline B|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters k₀ (radiusB y) (B).B_pos i z (by omega)).trans; rw [two_mul]
  · intro j hj he; exact if_neg he
  simp
end YM.LocalTaylorR2.Capstone
