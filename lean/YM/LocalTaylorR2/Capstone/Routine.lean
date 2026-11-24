import YM.LocalTaylorR2.Capstone.Crescent
/-! Concrete adapter at any Spring (simultaneously kinetic count at actual `.beta`) -/
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
section tube
variable {G:Gauge}{F:Lattice.Side}{A:Rep G F}{c:Clip}{b:BudgetPoint}{W:PathData G}{q:Listing G F} (u:Pipes G F) (x y z:Tap G F) {β τ Λ κ ε e c' w μ σ χ g C:ℝ} {δ μ':ℝ}
    (hx:A= Progress.DirectedRecipe.finish W c b u x β τ) (h0:x.regular-y.regular=z.regular)
def onto (A:Rep G F):={A with activities:=Capstone.varyP u x A.activities}
include hx h0 in
lemma strong (hv: A.Lawful χ C κ Λ μ) (h1:(u.pours x).Valid b σ w) (h2:(u.pours y).Valid b ε c') (h3:(u.pours z).Valid b e μ') :
    let V:=onto u y A; let Z:=onto u z A
    A.p=b ∧ A.activities.E-V.activities.E=Z.activities.E ∧ A.Lawful χ C κ σ μ ∧ V.Lawful χ C κ ε μ ∧ Z.Lawful χ C κ e μ ∧
    A.eval=V.eval*fun U'=>Real.exp (-(Z.activities.additive b U')):=by
  intro V Z
  have hz:A.p=b:=by rw [hx]; rfl
  have ha:A.activities.reg=(drawer G F).reg:=by rw [hx]; rfl
  have hh:A.activities.E=drawn u x:=by rw [hx]; rfl
  have ht:A.activities.Valid b Λ μ:= hz ▸ hv.labels
  have hp (y:Tap G F) {δ w: ℝ} (he:(u.pours y).Valid b δ w) : (onto u y A).Lawful χ C κ δ μ:= ⟨hv.paths, (Eq.mp (congrArg ((varyP u y A.activities).Valid · δ μ) hz.symm) (moveUp u y _ ha ht he))⟩
  have he:= hp x h1
  have hs : onto u x A=A:= by simp [onto,varyP,← hh]
  rw [hs] at he
  refine ⟨hz,?_,he,hp y h2,hp z h3, tollsUp u x A hz ha hh h0 (moveUp u y _ ha ht h2) (moveUp u z _ ha ht h3)⟩
  change A.activities.E - drawn u y=drawn u z
  rw [hh,pouring_reg u x h0,add_sub_cancel_left]
lemma book_up {A: Rep G F} (he:A.Lawful χ C κ ε μ)(hu: ε≤e): A.Lawful χ C κ e μ:=⟨he.paths,{he.labels with boundE:= Time.E_rises he.labels.boundE hu}⟩
lemma seats_era (A:Rep G F) : HasSlots b A.activities → HasSlots b (onto u x A).activities:=fun h=> sleepers u x A.activities h
lemma reckoner {a b x y p:ℝ} (h:a=p+b)(hq:b=x+y): a=p+x+y:=by linarith
lemma deliver_fee {a b c H y:ℝ} (h:a=b+c) (hp:y*|c| ≤ H): y*|a-b| ≤ H:=by rwa [h,add_sub_cancel_left]

lemma marks_era (h:A.p=b): (onto u x A).p=b∧ (onto u x A).beta=A.beta ∧ (onto u x A).path=A.path∧ (onto u x A).clip=A.clip∧ (onto u x A).v=A.v∧ (onto u x A).activities.reg=A.activities.reg ∧ (onto u x A).activities.K=A.activities.K ∧ (onto u x A).activities.forced=A.activities.forced := ⟨h,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
lemma third {p a:ℝ} (h0:0≤p)(hx:a≤p/2):p/32+a≤p:=by linarith
lemma allow_pos (X:Levels G)(n:ℕ) : 0≤ X.clock.allowance n:= Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
end tube
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
local notation "W"=> A.B.a.params m
local notation "R!"=> A.B.kin.path N m
local notation "Δ"=> Averaging.delta
local notation "a'"=> Time.fraction A.B.a m
local notation "K'"=> A.B.a.clock.forcedAllowance m
local notation "r" => H.result x
local notation "τ"=> (H.τ x)
local notation "U₀'"=> (H.X'.read)
local notation "e'"=> (A.B.a.clock.allowance m)
local notation "clo"=> A.B.a.clock.loopCap m
variable (hG:G.Simple) (hk:Mallow.RG12.Earned (checkD G) R.shape A.delay) (ε:ℝ) (he : 3*CalendarStep.loss (A.B.a.clock.J (m+1)) ≤ ε)
local notation "p'" => Collection.shelves H.X' R! B
abbrev era:= Collection.branch H.X' R! (W).clip B (sketch R H x p φ) (if φ then v else 0)
abbrev stanza : Rep G (A.B.a.S.side m n):= onto p' (era R H x p φ) r
def betaForecast := predictor A.B N Q x +Δ ((U₀') (sketch R H x p true))
local notation "Q₀" => stanza R H x p
local notation "Q₁" => H.τ x
abbrev Sizing {n:Lattice.Side} (X: Levels G) (m:ℕ) (F: Rep G n) (vC:ℝ): Prop:= F.Lawful (X.params m).width (X.params m).paths (X.clock.loopCap m) vC (X.clock.forcedAllowance m)
-- param `F: Rep G n` free uses A. prefer generic.
structure Priced (ε:ℝ) (rOp:ℝ) : Prop where
    marks (φ:Bool): (Q₀ φ|>.p)=B ∧ (Q₀ φ).beta=(r).beta ∧ (Q₀ φ).path=(r).path ∧ (Q₀ φ).clip=(r).clip ∧ (Q₀ φ).v=(r).v ∧
     (Q₀ φ).activities.reg=(r).activities.reg ∧ (Q₀ φ).activities.K=(r).activities.K ∧ (Q₀ φ).activities.forced=(r).activities.forced
    trunk : let e:= a*o; (H.V' x).logRead=(t true).logRead+(t false).logRead ∧ (H.V' x).hardRead=(t true).hardRead ∧ (H.V' x).hardRead=(t false).hardRead ∧ Collection.Local H.X' B (sketch R H x p true) (eH+e) K₀ ∧ Collection.Local H.X' B (sketch R H x p false) e K₀ ∧ e ≤ rOp
    count : (r).activities.E - (Q₀ true).activities.E=(Q₀ false).activities.E
    bill : Sizing A.B.a m (r) a' ∧ Sizing A.B.a m (Q₀ false) rOp ∧ Sizing A.B.a m (Q₀ true) (a'+rOp)
    extra : 3≤p → ε≤ 1 → Sizing A.B.a m (Q₀ true) (e')
    beta : (r).beta=betaForecast R H x p + Δ ((U₀') (sketch R H x p false))
    money : (B).threshold^2 * |(r).beta-betaForecast R H x p| ≤ rOp
    rooms φ : HasSlots B (r).activities → HasSlots B (Q₀ φ).activities
    clock : (r).p=B
    actual : (r).eval=(Q₀ true).eval*fun U' => Real.exp (-((Q₀ false).activities.additive B U'))
include hp hk he hG hx hY hm
variable {rOp:ℝ}
lemma stampNow (hc : y₁^requested (p+1) ε ≤ rOp): Priced R H x p ε rOp:=by
  let R₀:=H.result x
  let Z':= y₁^requested (p+1) ε
  let D':= H.X'; let v₀:= H.V' x; let W':= H.τ x
  let f:=(Collection.shelves D' R! B)
  let m':=Collection.branch D' R! (W).clip B v₀ v
  let r' σ:=(Q₀ σ).activities
  have h:= H.owns hG hm hx
  obtain ⟨hy₁,hℓ,hsp,hS,hQ₀,hQ,hQ₁,hw⟩:= rocket R H x hx p hp hY hm hG hk ε he
  have ht : m'.regular-(era R H x p true).regular=(era R H x p false).regular:= by simpa only [era,Bool.false_eq_true,ite_false,ite_true] using! hS.reg
  have hu₀: R₀.Lawful (W).width (W).paths clo (e') K':= ((H.moves hG hm).2 _ hx).1.bundle.valid
  have hf: (f.pours (era R H x p true)).Valid B (a'+Z') K₀:= by simpa only [era,ite_true] using! hQ₁.covers.labels
  have hf': (f.pours (era R H x p false)).Valid B Z' K₀:= by simpa only [era,Bool.false_eq_true,ite_false] using! hQ₀.covers.labels

  have hQ' : (f.pours m').Valid B a' K₀:= hQ.covers.labels
  obtain ⟨hz,hX,hS₀,hS₁,hS₂,hQ''⟩:= strong f m' _ _ (show R₀= Progress.DirectedRecipe.finish R! (W).clip B f m' (predictor A.B N Q x + Δ (U₀' v₀)) (Collection.vac v₀ (H.τ x)) from h) ht hu₀ hQ' hf hf'
  have hx' : R₀.beta= predictor A.B N Q x+ Δ (U₀' v₀):= Eq.trans (congr_arg RG.Rep.beta h) rfl
  have hlo : R₀.beta= betaForecast R H x p+Δ (U₀' (sketch R H x p false)):= reckoner hx' hy₁
  refine ⟨fun φ=> marks_era f (era R H x p φ) hz,?_,hX,⟨hS₀,book_up hS₂ hc,book_up hS₁ (add_le_add_right hc _)⟩,fun ht hs=>?_,hlo,(deliver_fee hlo hℓ).trans hc,fun φ=> seats_era f (era R H x p φ) _ , hz,hQ''⟩
  · obtain ⟨hr,hr₀,hr₁,hr',hr''⟩:= rebased R H x hx p hp hY hm
    exact ⟨hr,hr₀,hr₁,hr',hr'',hw.trans hc⟩
  have hi : a'+ Z' ≤ e':= third (allow_pos A.B.a m) (hsp ht hs)
  exact book_up hS₁ hi
end YM.LocalTaylorR2.Capstone
