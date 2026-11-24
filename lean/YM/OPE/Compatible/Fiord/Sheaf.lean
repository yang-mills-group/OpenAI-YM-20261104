import YM.OPE.Compatible.Fiord.Mint
/-!
# Marginal plans. True relative density jets, *before* normalization
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(U: Scaffold φ (Counters β) n (Mnd i S A) r)
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock Stranded
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
open ScriptJ
local notation "TC"=> Merchant.Chamber G r
section
variable {J:I→Type}[∀ i, MeasurableSpace (J i)]{μ:∀ i,Measure (J i)}[∀ i, IsProbabilityMeasure (μ i)]
variable (X:(i:I)→J i→Bid.Dir G (n i))(Y:(i:I)→J i→ Merchant.Chamber G r)
open Merchant.Sleeve.Scaffold
local notation "qK"=> KPole A
local notation "qL"=> LPole A
local notation "ΓZ"=> Counters β
local notation "V!"=> Punched A U
local notation "Q!"=> SkinQ n ΓZ μ φ
local notation "A!"=> SkyQ r ΓZ μ φ
variable (hp:SkinQ n (Counters β) μ φ X)(he: SkyQ r (Counters β) μ φ 0 Y)
local notation "xK"=> XTarg A X
noncomputable def OxT (q:GlyphQ G n) (k:ℕ):=TossK q (Punched A U) (Coach (KPole A) (Punched A U) X D) Y k
-- avoid PT cast
noncomputable abbrev Flex (i:I)(z:J i):= ExT A U D i (X i z) (Y i z)
local notation "Γ!"=> OxT A U D X Y
omit [∀ i, IsProbabilityMeasure (μ i)] [∀ i,MeasurableSpace (J i)] in
lemma γShape (j:I)(z:J j): let t:= Flex A U D X Y j z; let f:= OxT A U D X Y; t.l= -(f (KPole A) 2 j z+ f (LPole A) 0 j z)∧ t.h= -(f (KPole A) 3 j z+ f (LPole A) 1 j z):=by
       let u:= WField A U D X Y j z; let x:=WPush A U D X j z; let f(k:ℕ):=jet (KPole A j) k; let g(k:ℕ):=jet (LPole A j) k; intro t F
       have hj (q:GlyphQ G n)(k:ℕ): F q k j z=jet (q j) (k+1) u-jet (q j) (k+1) x:=by
          unfold F OxT TossK OpX; unfold Article u x WField WPush Sleeve.Coach; rw [WFul]
       rw [hj,hj,hj,hj]; have ht:t= PolV A j u-PolV A j x:=by
            unfold t Flex ExT u x WField WPush Sleeve.Coach; with_reducible_and_instances rfl
       rw[ht]; apply arP A j u x
where arP (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(j:I) (u x:Bid.Dir G (n j)) : let t:= PolV A j u-PolV A j x; let f(k:ℕ):=jet (KPole A j) k; let g(k:ℕ):=jet (LPole A j) k; t.l = -(f 3 u-f 3 x+(g 1 u-g 1 x))∧ t.h = -(f 4 u-f 4 x+(g 2 u-g 2 x)):=by
       intro t f g; constructor; · change - f 3 u - g 1 u-(- f 3 x-g 1 x) = -(f 3 u-f 3 x+(g 1 u-g 1 x)); ring
       change -f 4 u-g 2 u-(-f 4 x-g 2 x)= -(f 4 u-f 4 x+(g 2 u-g 2 x));ring
include h hp he hs hD
local notation "S!"=> Grain μ φ ΓZ
lemma coinΦ (k:ℕ): S! (OxT A U D X Y (KPole A) k) 0 ∧ S! (OxT A U D X Y (LPole A) k) 0:=by
       let Z:= Punched A U; let M:= WPush A U D X; let ht:=GainW A U D hs hD X hp; exact ⟨rentZ U _ _ (holdZ A U hs) Z M Y ht he le_rfl k, rentZ U _ _ (holdL A U hs h) Z M Y ht he le_rfl k⟩
lemma tapD (k:ℕ)(hc:c ≤ 0):
        let δ(q):= (Γ!) q k-OxT A U D (XTarg A X) Y q k
        Grain μ φ (Counters β) (δ (KPole A)) c∧ Grain μ φ (Counters β) (δ (LPole A)) c:=by
       intro v; let ht:=holdZ A U hs; let X':=Punched A U; let R:= Fractage S r; exact ⟨rentD U (KPole A) _ ht X' X Y hp he le_rfl D (KPole A) _ ht hD.obey R hD.rate k hc,rentD U (LPole A) _ (holdL A U hs h) X' X Y hp he le_rfl D (KPole A) _ ht hD.obey R hD.rate k hc⟩
lemma saleQ :
       let f:= Flex A U D X Y
       Grain μ φ ΓZ (fun i x=> (f i x).l) 0 ∧ Grain μ φ ΓZ (fun i x=>(f i x).h) 0:=by
        intro f; let ht(k:ℕ):= coinΦ A U D hs h hD X Y hp he k; let u(s k:ℕ):= (ht s).1.add (ht k).2 U.top.fair; let H(k l):= Grain.sub (Grain.const (μ:=μ) (RateLE.const 0 U.top.fair)) (u k l) U.top.fair; refine ⟨(H 2 0).shift ?_, (H 3 1).shift ?_⟩
        all_goals filter_upwards with i; funext x; first | exact (zero_sub _).trans (γShape ..|>.1|>.symm) | exact (zero_sub _).trans (γShape ..|>.2|>.symm)
lemma κFlip (hc:c ≤ 0):
       let f:= Flex A U D X Y; let q:=Flex A U D (XTarg A X) Y; Grain μ φ ΓZ (fun i x=>(f i x).l-(q i x).l) c∧ Grain μ φ ΓZ (fun i x=>(f i x).h-(q i x).h) c:=by
        intro f q; let ht(k:ℕ):= tapD A U D hs h hD X Y hp he k hc; let v(i j:ℕ):= (ht i).1.add (ht j).2 U.top.fair; let H(k l):= Grain.sub (Grain.const (μ:=μ) (s:=c) (p:=0) (RateLE.zero φ ΓZ c)) (v k l) U.top.fair; refine ⟨(H 2 0).shift ?_,(H 3 1).shift ?_⟩
        all_goals
              filter_upwards with i; funext x; simp only [Pi.sub_apply,Pi.zero_apply]; unfold f q; first | rw[(γShape ..).1,(γShape A U D (XTarg A X) Y _ _).1]; ring | rw[(γShape ..).2,(γShape A U D (XTarg A X) Y _ _).2]; ring
end
end YM.OPE.Owl.HillZ
