import YM.LocalTaylorR2.Capstone.Fettle
/-!
 # At the output desks actual paint before clover. Propeller and K budgets.
    Including exact provisional K (intermediate rent may live in forecastK, from which buys
    every digest at merger). Its fitting cannot be substituted without paying Moves.Part.*.
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
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical
section forms
variable {G : Gauge} {c n : Side} {B:BudgetPoint} {V:Listing G n} {x y: Collection.Source G n} {a b e f:ℝ}
variable {φ ψ δ: ℕ → Config G c→ℝ} {u:ℕ→ RegularAddress c}
lemma meadow_sub (h: Meadow.Budget B u φ a)(hp:Meadow.Budget B u ψ b)(hk : φ=δ+ψ): Meadow.Budget B u δ (a+b):=by
  obtain ⟨y₁,hw,hX⟩:=h; obtain ⟨w,hh,h⟩:=hp; have he:δ=φ-ψ:= by rw [hk,add_sub_cancel_right]
  refine ⟨y₁+w,fun i=>?_,fun j=>?_⟩
  · convert! budget_plus (hw i) (hh i) using 1; ext j; dsimp only [Pi.add_apply]; split <;> ring
  rw [he]; exact ⟨CouplingShape.reg_sub (hX j).1 (h j).1,CouplingShape.sup_sub (hX j).1 (h j).1 (hX j).2 (h j).2⟩
lemma budget_of_local (H:Collection.Local V B x a b): Meadow.Budget B V.reg x.logRead a:= by obtain ⟨f,hp,he⟩:= H.cheap; exact ⟨f,he,fun i=> ⟨H.smooth i,hp i⟩⟩
lemma mounted (hx:Collection.Local V B x a b) (he:y.hardRead=x.hardRead)(h:∃ Z:Pipes G n, ∃ d:Tap G n, Z.reg=V.reg ∧ d.regular=y.logRead ∧ ∀ s q, Nonempty ((Z.pours d).Moves s q))
    (hp:Meadow.Budget B V.reg y.logRead e): Collection.Local V B y e b:= by
   obtain ⟨Z,d,hA,hK,hF⟩:=h; obtain ⟨u,hu,hk⟩:=hp
   have hH: (V.read y).ForcedFamily B:=by unfold Listing.read; rw [he]; have hf:=hx.family; exact ⟨hf.sym,hf.symtest,hf.meas,hf.meas_test,hf.reads,hf.reads_test,hf.permit⟩
   refine ⟨fun i=>(hk _).1,hH,fun i j=>?_,⟨u,fun i=>(hk _).2,hu⟩,?_⟩
   · unfold Listing.read; rw [he,← hA, ← hK]; obtain ⟨D⟩:= hF i j; obtain ⟨σ⟩:=hx.transforms i j; exact ⟨⟨D.ep,σ.kp,D.reg_site,D.reg_support,σ.forced_support,σ.forced_inventory,σ.forced_tests,D.valuesE,σ.valuesK⟩⟩
   rw [he]; exact hx.expensive
end forms
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
variable (hY : p ≤ A.B.a.clock.J (m+1)) (hm:m<N)
local notation "a"=> Capstone.fare k₀ (A.B.a.params m) y
local notation "s"=> CalendarStep.loss j₁
local notation "o"=> (y₁^(requested (p+1) s))
local notation "ω"=> (Q x).beta
local notation "t"=> sketch R H x p
local notation "P₀"=> Rain.beacons H.H H.knows H.W d x
local notation "P₁"=> Rain.lights H.H H.knows H.W d x
local notation "f₀"=> Rain.uptick H.H d x
local notation "Ω"=> (fun i:Stars=>2*(Fintype.card (Site (Omo i)):ℝ)*o)
local notation "K₀"=>Time.forecastK A.B.a m R.scout ω
local notation "eH"=> Time.forecastE A.B.a m
lemma ribbons : ∃ Z':Pipes G Z, ∃ D₀:Tap G (A.B.a.S.side m n), Z'.reg=H.X'.reg ∧ D₀.regular=(sketch R H x p φ).logRead ∧ ∀ σ q, Nonempty ((Z'.pours D₀).Moves σ q) := by
  let f:= rigging R H x p φ
  let u':= rescue R H x p φ
  refine ⟨Rain.lens H.H, Marlin.bison f u' P₁, rfl,rfl,fun s' q=>?_⟩ -- tactic syntax
  have h: Nonempty ((H.H.doors.read f).Moves s' q) := brave (H.H.houses P) B (H.H.sister P) v p φ d s' q
  exact Marlin.reeds H.H.doors z (2*z) f u' P₁ s' q h.some
include hY hx hm hp
lemma rebased : let U':= sketch R H x p true; let V:= sketch R H x p false
    (κ).logRead=U'.logRead+V.logRead ∧ (κ).hardRead=U'.hardRead ∧ (κ).hardRead=V.hardRead ∧
    Collection.Local H.X' B U' (eH+a*o) K₀ ∧ Collection.Local H.X' B V (a*o) K₀ := by
  intro U' V
  obtain ⟨h₀,h₁⟩:= songs R H x p hp hY hm; obtain ⟨hf,hF⟩:= beaming R H x p hp hY hm; have h:= H.core hm x hx
  let d₀:=rigging R H x p; let f:=rescue R H x p
  have he: (κ).logRead=U'.logRead+V.logRead:= layout_add (P₀) _ _ P₁ hf h₁
  have ht:Meadow.Budget B H.X'.reg V.logRead (a*o):= by
    rw [← Capstone.tariff k₀ (A.B.a.params m) y o B ⟨rfl,rfl,rfl⟩]
    exact Marlin.reg_bison H.H.doors z (2*z) (d₀ false) (f false) P₁ h₀ hF
  have hv:= mounted h (show V.hardRead=(κ).hardRead from rfl) (ribbons R H x p false) ht
  refine ⟨he,rfl,rfl,mounted h rfl (ribbons R H x p true) ?_,hv⟩
  exact meadow_sub (budget_of_local h) ht he
local notation "W"=> (A.B.a.params m)
local notation "hi"=> (D.L j₁) -- shadows hypotheses! not used except explicit.
local notation "R!"=> A.B.kin.path N m
local notation "Δ"=> Averaging.delta -- Work
local notation "a'"=> Time.fraction A.B.a m
local notation "K'"=> A.B.a.clock.forcedAllowance m
open Recoil
variable (hG:G.Simple) (hk:Mallow.RG12.Earned (checkD G) R.shape A.delay) (ε:ℝ) (he : 3*CalendarStep.loss (A.B.a.clock.J (m+1)) ≤ ε)
include hG
local notation "τ"=> (H.τ x)
local notation "U₀'"=> (H.X'.read)
local notation "clo"=> A.B.a.clock.loopCap m
include he hk
lemma rocket : let U':= sketch R H x p true; let V:= sketch R H x p false; let σ:=H.V' x; let z₀:= y₁^requested (p+1) ε
    let e := a*o; let W':= Collection.softNeed G B (W).clip (W).width (W).paths
    ((Δ ((U₀') σ))=(Δ ((U₀') U')+Δ ((U₀') V))) ∧ (B).threshold^2 * |Δ ((U₀') V)| ≤ z₀ ∧ (3 ≤ p → ε ≤ 1 → z₀ ≤ A.B.a.clock.allowance m / 2) ∧
    Recoil.Difference H.X' R! (W).clip B σ U' V v ∧
    -- softHit bill pre movement, not consumed through H01. Exact hard for U,V and output H.result as it will be quoted
    Recoil.Stamped R! (W).clip B H.X' V (W).width (W).paths (clo) 0 0 0 z₀ K₀ (W' 0 e) ∧
    Recoil.Stamped R! (W).clip B H.X' σ (W).width (W).paths (clo) ω τ v a' K₀ (W' v eH) ∧
    Recoil.Stamped R! (W).clip B H.X' U' (W).width (W).paths (clo) ω τ v (a'+z₀) K₀ (W' v (eH+e)) ∧ e ≤ z₀:=by
  intro U' V σ z₀ e W'
  obtain ⟨hu,hv,hF,h',hP⟩:= Capstone.rebased R H x hx p hp hY hm; have ht:= H.core hm x hx
  have hj : Errands G (hi) k₀ (W) y s :=by rw [params_eq A.B.valid m]; exact hk _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  obtain ⟨⟨hY,hR⟩,hB'⟩:= limiting (hi) k₀ (W) y ε B s hj ⟨rfl,rfl,rfl⟩ (by rw [← beta_eq A.B.valid]; exact (A.B.a.fits.delayed _).le) he p -- beta
  rw [← beta_eq A.B.valid] at hY hR hB'
  have hA:= (R.machine.passes hm H.knows).1
  have hf:= (hA.fees _ hx).regular
  have ha:= CalendarStep.kineticFee hG ht h' hu
  have hh (u':Collection.Source G Z)(β α t₁ g:ℝ) (hQ:Collection.Local H.X' B u' g K₀): Recoil.Stamped R! (W).clip B H.X' u' (W).width (W).paths clo β t₁ α (regularNeed G B (W).clip (W).width (W).paths α g) K₀ (W' α g):= Recoil.stamp hQ hG (A.B.support.cap N m hm.le) hA.decent hA.width (Return.enough_room ..) β t₁ α
  refine ⟨?_,(Averaging.delta_bound hG hP.projects).trans hY,hB',painted ht hG v h' hu hv hF,enlarge (hh V _ _ _ e hP) hR le_rfl le_rfl,enlarge (hh σ ω v τ eH ht) hf le_rfl le_rfl,enlarge (hh U' ω v τ _ h') ?_ le_rfl le_rfl,hY⟩
  · exact eq_add_of_sub_eq' ha -- verify orientation
  have hz : regularNeed G B (W).clip (W).width (W).paths v (eH+e)=regularNeed G B (W).clip (W).width (W).paths v eH+regularNeed G B (W).clip (W).width (W).paths 0 e:=by simp only [regularNeed,abs_zero]; ring
  exact hz.trans_le (add_le_add hf hR)
end YM.LocalTaylorR2.Capstone
