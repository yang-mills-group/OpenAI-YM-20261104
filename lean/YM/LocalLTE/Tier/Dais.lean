import YM.LocalLTE.Tier.Table
import YM.LocalLTE.Furnace.Feed

/-! # All funded, one physical Script and prosody on it

Concrete dictionary, retained early payments. Not reweighted setter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {M : Metals G} {D : Rolls M.p} {U : Alloy M D} {bt : Baton G} {v w t : Return.Wages}
    {L : Targets M.p M.K} {p : ℕ→ℕ→JointLoad.Heir.Record} {V : Programs M.p} {F : ℕ→ℕ→Postage} {S : Time.Scouts (F:=F)} {r : ℕ→ℕ→ℕ} {b : ℕ→ℕ→Booth} {E : Expenses L} {H : ℕ→ℕ→Cafe} {Q : ℕ→ℕ→Clockwork.Menu} {a : ℕ→ℝ} {Y : Register D E w a}
    {J : ℕ→ℕ→Folio.Aux} {c c₁ c₂ : ℝ} {E₀ : ℕ→ℕ→Next.Scheduling.Exchange} {η : ℕ→ℝ} {q : UVNext.CouplingReset.ResetPrices}
    (h : Touring (C:=V) (B:=H) U bt v t r b Q p J Y S c E₀ q η)

local notation "X" => U.B
local notation "W" => U.delay
local notation "P" => M.p
variable (hh : Height.Rich Y c₁ U.delay) (hy : Height.Tenement Y U.delay) (hW : Pew v t V p r Y (wind Q) U.delay c₂)
    (hF : ∀ j i,StepStages j i → (M.p.profile i).supportExponent+3 ≤ (E j i).earn ∧ (M.p.profile i).supportExponent+3 ≤ t j i ∧ (L j i).halo+5 ≤ r j i)
    {N m n : ℕ} (hm : m<N) {I R : RG.Rep G (U.B.a.S.side (m+1) n)}
    (hl : Lives U.B.bake N (m+1) n R) (hb : R.beta∈band U.B.a (m+1)) (hc : Guide U.B Y N m n I) (hd : Guide U.B Y N m n R)
    (he : Opera.Price U.B Y N m n R hd) (ha : Alliance hc hd 1 0) (hx : ha.units=Equiv.refl _)
    (hf : I.path=R.path) (hf' : I.activities.reg=R.activities.reg) (hK : I.activities.forced=R.activities.forced)
local notation "a'" => U.B.a

variable {χ₀:ℝ} {χ₂:ℕ→ℕ→ℝ} (hP:PewT v t V p r Y (Roof.wind Q) U.delay χ₂) (FP:ℕ→ℝ)
local notation "I₀" => U.B.a.clock.J m
local notation "J₁" => U.B.a.clock.J (m+1)
local notation "F₀" => (D.L (J₁))
local notation "T0" => U.B.a.clock.hatBeta m
local notation "B" => U.B.a.budget m
-- schedule post obtains crew for amplitude. Extent costs need extra pre-L inside χ₂.
abbrev slew (j i:ℕ)(x α e:ℝ):Prop:= Balloons (E j i) (D.L j) (w j i) (Y.μ j i) α (Y.c j i) x e 3 (M.p.profile i).order (M.p.profile i).power Chi.canonical (Y.o j i)
local notation "EP"=> incomingE G F₀ T0
include hm hP hl h hb hF
lemma defray (ha:Pumps R FP (χ₀*(EP))) (hp:slew (Y:=Y) J₁ I₀ T0 χ₀ (-(9/8:ℝ))) :
    ∃ f₁ : hd.fragrances → ℝ, (∀ i:hd.fragrances, Height.ancestry i → (B).Regular (Beam.dashboard hd i).support (sequence hd (Meadow.intern hd) Chi.canonical i)∧ (B).supBounds (Beam.dashboard hd i).site (Beam.dashboard hd i).support (sequence hd (Meadow.intern hd) Chi.canonical i) (f₁ i)) ∧
    let X₀ (z:hd.fragrances):=if Height.ancestry z then rocket hd FP z * f₁ z else 0
    early B (Beam.dashboard hd) (fun z=> if z∈Set.range (Brim.icon hd)∧ Beam.nearbound z then X₀ z else 0) (χ₂ (J₁) (I₀) * (χ₀ * EP) + χ₂ (J₁) (I₀) * (χ₀ * EP))∧
    Ac.Hit (Captain.reachability (H:=hd)) (B).B (fun z=> if z∈Set.range (Brim.icon hd)∧ Beam.nearbound z then 0 else X₀ z) ((E (J₁) (I₀)).earn) (betaF G T0 F₀ ^ (-(9/8):ℝ)) := by
  let x:=U.B.a.clock.hatBeta m; let C:=U.B.a.clock.J m; let u:=U.B.a.clock.J (m+1); let K:=M.p.profile C
  have hi: StepStages u C:= step_paid U.B.a m
  have hk := U.B.valid.pays m
  let T:= ships X N m n; obtain ⟨Y',d,v',t',A',b',r',B',q',z',G',hX⟩:= hp _ _ _ T hd.laws.data.funds (protocol X hm h.full) _ hd FP ha
  have hR : U.B.a.params m=K:= params_eq U.B.valid m
  have hp : (B).power=K.power :=congr_arg RG.Stage.power hR
  have hj : (B).order=K.order :=congr_arg RG.Stage.order hR
  obtain ⟨hz',ht,hr⟩:=hF u C hi
  have ht':preExponent B= K.supportExponent+3 := congr_arg (fun s:RG.Stage=>s.supportExponent+3) hR
  have hh' := hP _ _ hk _ hi (first_le U.B.valid m) T
  let desk := assigned h.hearing.plan m n X N R
  have he₀:= (Psalm.Stage.directed h.hearing X hm hb hl (fun m' h'=> h.full _ _ _ (by simp at h'; omega))).1.enabled
  have hz₀ := he₀.make; obtain ⟨hp₀,hc'⟩:= he₀.pre; have hf₁ := (he₀.clocks R.beta hb).2
  have hh₀ : desk.profile=wind Q u C:= rfl
  rw [← hl.point] at hp₀ hc' hz₀ hf₁ -- hc shadow?
  have hh : U.B.a.S.block m=D.L u:= PriceCompiler.block_eq U.B.valid m
  have he₁ : Hauses FP hd (p u C) desk.broadCut desk.profile Chi.canonical desk.radius B (Solo.raise t u C) (χ₂ u C *(χ₀*EP)) (χ₂ u C *(χ₀*EP)):=
    hh₀.symm ▸ hh' hd.laws.data.funds R _ _ hd B rfl hp hz₀ hr (hh ▸ hp₀) (hp ▸ hc') (hh ▸ hf₁) _ le_rfl _ _ _ _ _ _ _ _ _ _ G' desk.broadCut desk.radius FP _ ha
  exact Beam.crest FP ha.1 G' hX he₁ rfl (ht'.trans_le (ht.trans (le_add_of_nonneg_right (by norm_num)))) rfl hj.le (show (B).power≤K.power from hp.le) -- need last?
end YM.PhysicalNext.Repeat.Roof
