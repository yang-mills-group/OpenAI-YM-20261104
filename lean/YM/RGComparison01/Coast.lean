import YM.RGComparison01.Ocean

/-!
# An exact unmarked pre-reset representation

 Pointwise, with budget footprint +3 after changing dashboard sites. In
 particular it's still the complete density including forced `K`, with
 literal analytic and exceptional Weeds. No empty-root gas estimate thrown
 away. Soft piece price before analytic comparison is *not* being claimed
 improved. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Coast
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe
open PhysicalNext PhysicalNext.Repeat Height Song Time Opera
open Divides Selector Coin High Plev Quests
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} (F : Roost.Factor A)
variable {c f : Side} {m N : ℕ} (sizes : f.val=c.val*(A.B.a.S.block m).val)
    {R : Rep G f} (H : Boulevard.Chartlet F.shape A N m sizes R)
local notation "I" => A.B.a.clock.J m
local notation "J" => A.B.a.clock.J (m+1)
local notation "S" => Pane.panel A m sizes
local notation "L₀" => (D.L J)
local notation "Q₀" => (F.target J I)
local notation "sP" => (X.p.profile I)
local notation "expn" => (F.expense J I)
local notation "θ₀" => (A.B.a.clock.hatBeta m)
local notation "μ₀" => (F.shape.μ J I)
local notation "T" => (Pane.orchestra A N sizes)
local notation "θv" => betaF G θ₀ L₀
local notation "gZ" => Height.grow G L₀ θ₀
local notation "γ" => A.B.kin.alpha N m
local notation "p" => A.B.a.budget m
local notation "O" => Chi.canonical
local notation "aH" => (selfA H)
local notation "Y₀" => (Beam.marquee H p)
local notation "P₀" => (Song.plusone H (aH) O γ)
variable (Ω : ℕ→Prop) (k : ℕ)

def kept (i : Magazine H) := ¬ (meter H Ω (countOrder k) (p).B i ∨ Divides.hires H Ω i)
def kept_out := fromPost F sizes R H (kept F sizes H Ω k) γ
abbrev inherited := fromPost F sizes R H (Divides.hires H Ω) γ
abbrev weeded := fromPost F sizes R H (meter H Ω (countOrder k) (p).B) γ

lemma posts_id (K : Magazine H→Prop) (i : ℕ) : (fromPost F sizes R H K γ).logRead i =
    if K (pennant H i).2 then (P₀).logRead i else 0 := by
  let s:= (pennant H i).2
  unfold fromPost choir; simp only [Function.comp_apply, bySong]
  split
  · rfl
  ext; simp

lemma sumId (i : ℕ) : (P₀).logRead i=(kept_out F sizes H Ω k|>.logRead i)
      + (inherited F sizes H Ω|>.logRead i) + (weeded F sizes H Ω k|>.logRead i) := by
  let s:= (pennant H i).2
  have hp : Divides.hires H Ω s → ¬meter H Ω (countOrder k) (p).B s:= by
    suffices h : ∀ s:Magazine H,Divides.hires H Ω s → ¬meter H Ω (countOrder k) (p).B s from h s
    rintro (s|s) hs
    · exact fun h=> (show ¬Inherited Ω s ∧ _ from h).1 hs
    exact False.elim hs
  unfold kept_out inherited weeded
  rw [posts_id,posts_id,posts_id]; change _= (if kept F sizes H Ω k s then _ else _) + (if Divides.hires H Ω s then _ else _) + (if meter H Ω (countOrder k) (p).B s then _ else _)
  by_cases hh : Divides.hires H Ω s; · simp [kept,hh,hp hh]
  by_cases ht: meter H Ω (countOrder k) (p).B s <;> simp [kept,ht,hh]

lemma portioning {b v : ℝ} (M : Magazine H→Prop)
    (h : Collection.Local Y₀ p P₀ v b) : Collection.Local Y₀ p (fromPost F sizes R H M γ) v b:= by
  obtain ⟨f,hf,hF⟩:=h.cheap
  let U:= fromPost F sizes R H M γ
  have ht (i:ℕ) : (P₀).logRead i=U.logRead i ∨ U.logRead i=0:= by unfold U; rw [posts_id]; split <;> simp
  obtain ⟨g,hg,hQ⟩:= Meadow.emptyFree _ p (u:=(P₀).logRead) ⟨f,hF,fun i=>⟨h.smooth i,hf i⟩⟩ U.logRead ht
  have hF:= h.family; exact ⟨fun i=> (hQ i).1, ⟨hF.sym,hF.symtest,hF.meas,hF.meas_test,hF.reads,hF.reads_test,hF.permit⟩,
    fun i b=> Beam.moves H p O aH i b _,⟨g,fun i=>(hQ i).2,hg⟩,h.expensive⟩

lemma coast {b y z w : ℝ} (h : Collection.Local Y₀ p P₀ y b)
    (hv : Meadow.Budget p (Y₀).reg (inherited F sizes H Ω).logRead z)
    (hw : Meadow.Budget p (Y₀).reg (weeded F sizes H Ω k).logRead w) :
    Collection.Local Y₀ p (kept_out F sizes H Ω k) y b ∧
      ((Y₀).read (inherited F sizes H Ω)).EBound p z ∧
      ((Y₀).read (weeded F sizes H Ω k)).EBound p w ∧
      ((Y₀).read P₀).KBound p b ∧
      ∀ β μ : ℝ,∀ V,
        earlyValue Y₀ (T).down (T).low p P₀ β μ γ V = earlyValue Y₀ (T).down (T).low p (kept_out F sizes H Ω k) β μ γ V *
          Real.exp (- ((Y₀).read (inherited F sizes H Ω)).additive p V - ((Y₀).read (weeded F sizes H Ω k)).additive p V) := by
  have hf:= LogSplit.unweighted p hv
  have ht:= LogSplit.unweighted p hw
  obtain ⟨g,hg,hK⟩:= h.expensive
  let Y:=Y₀; let B:=p
  let X:= P₀; let h₀ := kept_out F sizes H Ω k; let A₁ := (Y₀).read (inherited F sizes H Ω); let A₂:=(Y₀).read (weeded F sizes H Ω k)
  have hz:= portioning F sizes H (kept F sizes H Ω k) h
  refine ⟨hz,hf,ht,⟨g,hg,Payments.drop_reserve p _ (fun i=>(hg i).1) hK⟩,fun β μ V=>?_⟩
  let A₀:= Y.read h₀
  let f:= (Y.read X).additive B
  have he : f V=A₀.additive B V+(A₁.additive B V+A₂.additive B V):= by
    have hx : A₀.EBound B y:= by obtain ⟨v,hv,ht⟩:=hz.cheap; exact ⟨v,hv,Quotes.segment _ (fun i=>(hv i).1) ht⟩
    have ha:= Next.Rank.Alarm.ante B A₁ hf V; have hb:= Next.Rank.Alarm.ante B A₂ ht V
    have hc i : (Y.read X).regularOccurrence B i V=A₀.regularOccurrence B i V+(A₁.regularOccurrence B i V+A₂.regularOccurrence B i V):= by
      let y₀ := (Y.reg i).support
      change masked B.threshold y₀ ((P₀).logRead i) V=masked B.threshold y₀ ((kept_out F sizes H Ω k).logRead i) V + (masked B.threshold y₀ ((inherited F sizes H Ω).logRead i) V + masked B.threshold y₀ ((weeded F sizes H Ω k).logRead i) V)
      by_cases hp : Healthy B.threshold y₀ V
      · simp only [masked_eq _ _ _ _ hp]; rw [sumId F sizes H Ω k]; exact add_assoc _ _ _
      simp only [masked_ne _ _ _ _ hp,add_zero]
    unfold f Activities.additive; rw [← ha.tsum_add hb, ← (Next.Rank.Alarm.ante B A₀ hx V).tsum_add (ha.add hb)]; exact tsum_congr hc
  let t := (Real.exp (-γ*Collection.receipt (T).down (T).low p V))
  let b:= μ * Fintype.card (Site c) - (T).down.inChannels (T).low p β V
  let y:=(Y.read X).gas B V
  change Real.exp (b-f V)*y*t = Real.exp (b- A₀.additive B V)* A₀.gas B V*t * Real.exp (-A₁.additive B V-A₂.additive B V)
  have ha : y=A₀.gas B V:=rfl
  rw [ha,he,show b-(A₀.additive B V+(A₁.additive B V+A₂.additive B V))= (b-A₀.additive B V) + (-A₁.additive B V-A₂.additive B V) by ring,Real.exp_add]; ring

-- auxiliary also on own Board (smaller K always at suitable β).
lemma silent : Meadow.Budget p (Y₀).reg (inherited F sizes H (fun _=>False)).logRead 0 := by
  let K : Magazine H → Prop:= Divides.hires H (fun _=>False)
  have hg z : ¬ K z:= by rintro h; rcases z with z|z; obtain ⟨ps,hp,hP⟩:=h; exact hp; exact h
  have hx i : (inherited F sizes H (fun _=>False)).logRead i=0:= by unfold inherited; rw [posts_id, if_neg (hg _)]
  rw [funext hx]; refine ⟨fun i=>0,fun i=> by simp [SumBudget],fun i=>?_⟩
  exact ⟨CouplingShape.reg_const _, sup_le (CouplingShape.sup_const _) (abs_zero).le⟩
end YM.RGComparison01.Coast
