import YM.Integration.WilsonOlderFreshSoftSocketDeposit
import YM.Integration.WilsonReceivedFixedDigitFinite

/-! One socket planting factor follows every original fine child, through all ordinary proper faces and all measured kinetic reparametrizations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketCourse
open Function Finset Lattice Wilson RG Source Labels Comparison.RG02
open Laurent Bloch Precision WilsonCoeffUV.Blue WilsonCoeffUV.Power Work.F08 AnalyticNext.QuarticMatch.Sheets MultiNext.SignedSource Tree
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos
open OriginalMarkedSourceComet IndependentSourcePathFamily WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVerseRegister (offer start)
open FormalBulk08 WilsonCoeffUV.Winding PhysicalNext.Repeat.Legato
open WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I]{D:I→ℕ}

abbrev printed (Y:Outerm G D)(S:Finset I)(f:Pen D S→L[ℝ]ℝ)(x:I → Cover):Era G ℝ:=
  tuftV f (levelsO (Y x) S)

theorem travelled (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (k:I→ℕ)(N:ℕ)(c:Digits L I)(S:Finset I)(f:Pen D S→L[ℝ]ℝ)
    (Y Z:Outerm G D)(high:Wellness k Y)(low:Wellness k Z)(C:Cost)
    (incoming:∀x n,(printed Y S f x).1 n=affix C ((printed Z S f x).1 n))
    (days m:ℕ)(cut:m+days≤N):
    ∀x n,(printed (itinerary L O k N c days m Y) S f x).1 n=
      affix (clock L O N (m+days) m C) ((printed (itinerary L O k N c days m Z) S f x).1 n):=by
  induction days generalizing m with
  | zero=>
    intro x n
    rw [Nat.add_zero,clock,dif_neg (lt_irrefl m)]
    exact incoming x n
  | succ t ih=>
    intro x n
    let y:=chartIn (loose L m) x (c m)
    let P:=itinerary L O k N c t (m+1) Y
    let Q:=itinerary L O k N c t (m+1) Z
    have up:m+1+t≤N:=by omega
    have live:m<N:=by omega
    have pp:Eu k (P y):=(sound L O k N c simple ratio Y high t (m+1) up).level' y
    have qq:Eu k (Q y):=(sound L O k N c simple ratio Z low t (m+1) up).level' y
    have ph:=placedO (P y) pp S
    have qh:=placedO (Q y) qq S
    change (tuftV f (levelsO (logO L O m N (P y) k) S)).1 n=
      affix (clock L O N (m+(t+1)) m C) ((tuftV f (levelsO (logO L O m N (Q y) k) S)).1 n)
    rw [step_S L O m N (P y) k live simple ratio pp,step_S L O m N (Q y) k live simple ratio qq]
    change (tuftV f (verseI L O m N (mass k S) (levelsO (P y) S))).1 n=
      affix (clock L O N (m+(t+1)) m C) ((tuftV f (verseI L O m N (mass k S) (levelsO (Q y) S))).1 n)
    rw [Mer.ply_verse L live simple ratio ph f,Mer.ply_verse L live simple ratio qh f]
    rw [show m+(t+1)=m+1+t by omega,clock,dif_pos (show m < m+1+t by omega)]
    exact WilsonOlderFreshSoftSocketHistory.step L O simple ratio N m (mass k S) live _ _ _
      (qh.tuft f) (ih (m+1) up y) n

variable (R:Run G)(d:I→ℕ)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(q:(i:I)→Choice R d i)
local notation "hi_" => WilsonOlderFreshSoftSocketPole.raw R d κ pt q
local notation "lo_" => WilsonReceivedCanonicalVerseRegister.offer R d κ pt q
local notation "lag_" => WilsonOlderFreshSoftSocketPole.lag R d q

theorem original (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N:ℕ)(c:Digits L I)(S:Finset I)(f:Pen D S→L[ℝ]ℝ)(days m:ℕ)(cut:m+days≤N)(x:I → Cover):
    let H:=printed (itinerary L O d N c days m (independent (hi_))) S f x
    let Z:=printed (itinerary L O d N c days m (start R d κ pt q)) S f x
    let b:=clock L O N (m+days) m (PowerSeries.X^(∑i∈S,lag_ i))
    (∀n,H.1 n=affix b (Z.1 n)) ∧ H.2=affix b Z.2:=by
  intro H Z b
  have h:Wellness d (independent (hi_)) :=(OriginalCoverReanchoring.deposited (hi_) (fun _ _=>Nat.le_add_left _ _)).1
  have l:Wellness d (start R d κ pt q):=(OriginalCoverReanchoring.deposited (lo_) (fun j _=>WilsonReceivedCanonicalVerseBasis.grade R d κ pt j (q j))).1
  have hit:=travelled L O simple ratio d N c S f _ _ h l _ (fun y n=>WilsonOlderFreshSoftSocketDeposit.original R d κ pt q y S f n) days m cut x
  have ph:Auth (mass d S) H:=(placedO _ ((sound L O d N c simple ratio _ h days m cut).level' x) S).tuft f
  have qh:Auth (mass d S) Z:=(placedO _ ((sound L O d N c simple ratio _ l days m cut).level' x) S).tuft f
  exact ⟨hit,WilsonOlderFreshSoftSocketHistory.cover _ _ _ ph qh hit⟩

end YM.Integration.WilsonOlderFreshSoftSocketCourse
end
