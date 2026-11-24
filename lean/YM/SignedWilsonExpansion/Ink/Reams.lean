import YM.SignedWilsonExpansion.Chron.Ballots
import YM.SignedWilsonExpansion.Chron.Orris
import YM.SignedWilsonExpansion.F9.Crops
import YM.Integration.WilsonIndependentCollarOrdinaryCruise
import YM.Integration.WilsonReceivedCanonicalVersePortfolio
/-! `stop` power series on **literal independent estimator of purchased terminal**, and equivalence to our roster perspective. All masks retained on fitted names and exact site. Use `Orris`. Auxiliary inversion from launched terms uses these *same* leading thermal values.
-/
set_option quotPrecheck false
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Integration.Liner
open Function Matrix Lattice RG Laurent Bloch Gauge
open WilsonCoeffUV WilsonCoeffUV.Blue FreeResolvent Tree WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Power
open WilsonCoeffUV.Bank WilsonCoeffUV.Soil Exterior Source WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Mer.Xa
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark Lattice Laurent Labels Precision PowerSeries
open WilsonCoeffUV.Bank.Mosaic
open PhysicalNext.Repeat.Legato Wilson Stationary Finset
open OriginalMarkedSourceComet IndependentSourcePathFamily
open ActualRunCurvaturePackets WilsonCoeffUV.Mer.Xa.Corps MarqueQ MarqueQ.Crops WilsonCoeffUV.Winding
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open WilsonReceivedCanonicalVerseRegister (start offer)
open WilsonReceivedFixedDigitHistory
open SignedWilsonExpansion.Commission Pert.Asymptotics
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type} [Fintype I][DecidableEq I]{k N K m p v c e n:ℕ}{A:Levels G}
open Ballots
local notation "ι'" => Fin (n+1)
namespace InkP
variable (R:Run G)(d:I→ℕ){D:I→ℕ}(pt:I→Chamber)(N p v K:ℕ)

def scout (S:Finset I)(q:Selection R d S)(i:I): Cursor R (d i):= if h:i∈S then q ⟨i,h⟩ else .inl ()
-- entering estimator term no pole loss forgotten
local notation "A₀"=> R.family.path.levels
local notation "L₀"=> R.metals.O
local notation "g"=> regulatorRun R.family N p
local notation "σ"=> (((R.family.path.rep N p K).p.threshold):ℝ)

abbrev inT (f:(i:I)→ Cursor R (d i)):Outerm G D:=start R d (fun i=> knob (D i)) pt f
abbrev Pole (f:(i:I)→ Cursor R (d i))(S:Finset I) (c:ℕ)(tape:Digits R.family.path.levels I)(y:I → Cover) := cruises A₀ L₀ N (mass d S) c v (tuftV (touch (lamp D) S) (levelsO (itinerary A₀ L₀ d N tape (K-c) c (inT R d pt f) y) S))
abbrev Ladder (S:Finset I) (o:I→Site (R.family.side K p)) := digits R.family.S p K o
-- Liner

def forecast (c:ℕ)(x:(i:I)→ R.family.label (d i))(t:Digits R.family.path.levels I)(y:I→ Cover)(S:Finset I) : InkQ:=
  ∑ q:Selection R d S,(weight R d N p K x S q) • insertQ (dew (Pole R d (D:=D) pt N v K (scout R d S q) S c t y))

def valued (c:ℕ)(x:(i:I)→ R.family.label (d i))(o:I→ Site (R.family.side K p))(S: Finset I): InkQ:= forecast R d (D:=D) pt N p v K c x ( Ladder R p K S o ) (address A₀ ( Ladder R p K S o ) (c-v) v 0) S
lemma ramp (r:ℕ) (t:Digits A I)(y:I→ Cover)(s:ℕ): address A t s r y=Ballots.routeX A.S t s r y:=by
    induction s generalizing r y with
    | zero=> rfl
    | succ n ih=> exact ih (r+1) _
lemma pigmentV {p₁:I} (f:Choice R d p₁)(x:(i:I)→ R.family.label (d i)) : WilsonReceivedCanonicalVerseBasis.basis R d (fun i=> knob (D i)) pt p₁ f= petS R (d p₁) (D p₁) (pt p₁) f ∧ WilsonReceivedCanonicalVerseBasis.dose R d N p K x p₁ f=stick R (d p₁) (g K) σ (x p₁) f:=by cases f <;> constructor <;> rfl
lemma stencilV (u:G.Simple)(h:LocalRatio L₀)(t:K≤ N)(x: v ≤ c)(w:c≤ K)(S:Finset I)(o:I→ Cover)(ξ':Digits R.family.path.levels I)(y:I→ Cover)(p': address A₀ ξ' (K-c) c y=o)(f:(i:I)→ Cursor R (d i)): dew ( Pole (D:=D) R d pt N v K f S c ξ' y )= FadeRaw A₀ L₀ N (mass d S) v K (tuftV (touch (lamp D) S) (levelsO (inT R d pt f o) S)):=by
    have hu:= WilsonIndependentCollarOrdinaryCruise.original A₀ L₀ u h N ξ' (inT R d pt f) ( ( OriginalCoverReanchoring.deposited (offer R d (fun i=> knob (D i)) pt f) (fun i _=> WilsonReceivedCanonicalVerseBasis.grade R d _ pt i ( f i ) ) ).1 ) S (touch (lamp D) S) (K-c) c y (show c+(K-c)≤N by omega)
    rw [p',Nat.add_sub_of_le w] at hu; rw [Pole,hu, ←cruisesMore]; assumption'
lemma signalsT (e:ℕ)(S:Finset I)(ξ:(i:I)→ Site ( R.family.side K p ))(x:(i:I)→ R.family.label (d i)) :
 calcT (g v:ℂ) e (valued R d (D:=D) pt N p v K c x ξ S)= ∑ q:Selection R d S,weight R d N p K x S q*(((∑ i∈ range (e+1), (g v)^i*(Pole R d (D:=D) pt N v K (scout R d S q) S c ( Ladder R p K S ξ ) (address A₀ ( Ladder R p K S ξ ) (c-v) v 0)).2 i 0 Fin.elim0) :ℝ):ℂ):=by
    rw [valued,forecast,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul, smul_eq_mul]; congr 1; rw [timed]; push_cast; apply Finset.sum_congr rfl; intro j _; rw [inked,dew_coeff,mul_comm]
private lemma unsealA (c:Selection R d Finset.univ)(i:I): scout R d _ c i=c ⟨i,mem_univ _⟩:= dif_pos (mem_univ _)
lemma earnFit (f:Selection R d Finset.univ)(x:(i:I)→ R.family.label (d i)):
  weight R d N p K x Finset.univ f=∏ i:I, stick R (d i) (g K) σ (x i) (scout R d Finset.univ f i):=by
     unfold WilsonReceivedCanonicalVersePortfolio.weight; simp_rw [unsealA]; rw [ ←Finset.prod_coe_sort (s:=Finset.univ) (f:=fun i:I=>stick R (d i) (g K) σ (x i) (f ⟨i,mem_univ _⟩)) ] -- equiv subtype Set.univ
     exact Finset.prod_congr rfl (fun i _=>(pigmentV R d (D:=fun _=>1) (fun _ : I=> zeroC) N p K (f i) x).2)
def SealEq (d:I→ℕ): Selection R d Finset.univ≃ ((i:I)→ Choice R d i) where
   toFun x:=scout R d _ x
   invFun x i:= x i
   left_inv x:= funext fun i=> unsealA R d x i
   right_inv x:= funext fun i=> unsealA R d _ i
end InkP
section full
open InkP
variable (R:Run G)(D d: Fin (n+1)→ℕ)(pt:Fin (n+1)→ Chamber)
local notation "Ω"=> R.family.localSection
local notation "J"=> R.family.path
local notation "ħ"=> regulatorRun R.family N p K
local notation "T'"=> (((R.family.path.rep N p K).p.threshold):ℝ)
lemma familyEntire (u:G.Simple)(b:LocalRatio R.metals.O)(w:v≤c)(z:c≤K)(h:K≤N)(p:ℕ)(ξ:Digits R.family.path.levels (Fin (n+1)))(y o:Fin (n+1)→ Cover)(x: (i:Fin (n+1))→ R.family.label (d i))(hA: Ballots.routeX R.family.S ξ (K-c) c y=o) :
   forecast R d (D:=D) pt N p v K c x ξ y Finset.univ = phi R D d pt o (regulatorRun R.family N p K) ((R.family.path.rep N p K).p.threshold) x R.family.path.levels R.metals.O N v K:=by
      unfold InkP.forecast phi; rw [ ←Equiv.sum_comp (SealEq R d) ]; apply Finset.sum_congr rfl; intro i _
      simp_rw [earnFit]; -- try
      change _ • _= _ • _; congr 1; refine congr_arg insertQ ((stencilV R d (D:=D) pt N v K u b h w z _ o ξ y ( (InkP.ramp ..).trans hA ) (scout R d Finset.univ i)).trans ?_)
      let f:=scout R d Finset.univ i; have hv:inT R d (D:=D) pt f= trailG R D d pt f:= by apply congr_arg independent; funext j ν; exact ( pigmentV R d (D:=D) pt N p K ( f j ) x ).1
      rw [show inT R d (D:=D) pt (scout R d Finset.univ i)= trailG R D d pt f from hv]; rfl
/-- Main endpoint §(27). Actual tail. Hide `parent=0 at c` through purchase. -/
lemma entire (u:G.Simple)(b:LocalRatio R.metals.O)(w:v≤c)(z:c≤K)(o: Fin (n+1)→ Cover)(hu:∀ i,d i≤ k):
   ∀ᶠ p in Filter.atTop, rolls R.family.S (wrap (R.family.side K p) ∘ o) z=0 → ∀ N:ℕ, K≤N → ∀ x: (i:Fin (n+1))→ R.family.label (d i), valued R d (D:=D) pt N p v K c x (wrap (R.family.side K p) ∘ o) Finset.univ = MergeTrip.dockD d (fun i=> Ω (d i)) (fun i=> life R (d i) (regulatorRun R.family N p K) ((R.family.path.rep N p K).p.threshold) (x i)) R.family.path.levels R.metals.O N k v K o := by
      filter_upwards [Ballots.confirmed R.family.S o w z] with p hp y N hb x
      rw [valued,InkP.ramp]; exact ( familyEntire R D d pt u b w z hb p _ _ _ x (hp y) ).trans ( bridge R D d pt o _ _ x _ u b ( w.trans z ) hb hu )
end full
end YM.Integration.Liner
