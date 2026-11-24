import YM.OPE.Compatible.Lady.Riff
/-! # pan book scales before accepting. interior selection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
section
open Pressure ConnectedActivityE6 Shell Channel
variable {m:ℕ}{P:Teller G}{D:RG.Patch}{E:ConnectedActivityE6.Target G P}{Q:Side} {W C η:ℝ} {o:ConnectedActivityE6.Target.Order G W}
variable {L:I→Host K T}{p:∀ i,Wall D E Q o η C m (L i)}{V A:I→ℝ}{l:Filter I} {b e r' c C':ℝ}
variable (h: Chase (Eve p) l) {d:I→ℕ}(hn: Lite (Eve p) l (fun i=>‖(p i).w‖))
local notation "ζ"=> Eve p
local notation "ψ"=> Chase.σW (Eve p)
set_option quotPrecheck false
local notation "δA"=> fate (Eve p)
variable (x:∀ i,Site (L i).c)(v n:ℕ) {f:∀ i,AxisChart G (L i).ForestQ}
variable (hd: Lite (Eve p) l (fun i=>(d i:ℝ)))(hq:∀ᶠ i in l, Brite (rink (x i)) (p i).w (d i))
variable (hb:∀ᶠ i in l, Scale (fansU x p d n f i) (Ψs p v i)∧ Stowed (Hpools x d i) (f i)∧∀ j∉ (pond x p d n i).H,f i j=0)
variable (hS:∀ᶠ i in l, (L i).Rich s c e (A i) u C' ∧ 0 ≤ A i)(hT:0<s)(he:0<e)(hc:0≤c)(ht:RateLE l (fate (Eve p)) A 0)
local notation "p'"=> fansU x p d n f
variable (t:ℕ){N:ChartRatio G}(s':ℝ)(H:StackP N r R s')(hN:LocalRatio N)(hs:G.Simple)
variable {F:∀ i, Viewer (L i)} (P':Spells.Pad G)
variable (hp:∀ᶠ i in l,(F i).P=P' ∧ (F i).U=(L i).P.p ∧ pledgesF (Spindle.patch (F i).k (F i).x) (Hpools x d i))(hf:Lite (Eve p) l (fun i=> ((F i).k:ℝ))) (hF:∀ᶠ i in l, Viewer.Pledge (F i) (V i) (k+6)) (hU:RateLE l (fate (Eve p)) (fun i=>(F i).α (k+6) (Chase.σW (Eve p) i) (V i)) 0) -- ψ not recognized
variable (J:∀ i,World (L i).ForestQ ((pond x p d n i).H) G) (hJ:∀ᶠ i in l,Poured (Hpools x d i) (pond x p d n i).H (J i) (f i) (Chase.σW (Eve p) i) ∧ Measurable (Arbor (p i).glare.V (L i).P (L i).k (Hpools x d i) (pond x p d n i).H (WinK p t i) (J i)))
variable (hz:∀ q:ℝ,0≤ q→∀ᶠ i in l, crestPrice G (q*fate (Eve p) i)+Pξ G s c u C' (Ψs p v i)< WinK p t i/(2*Chase.σW (Eve p) i))
local notation "o'"=> (fun i=> Viewer.PatchT (fansU x p d n f i) (F i))
local notation "T!"=> fun i=> Viewer.scoreV (F i) (ψ i)
local notation "ΣT"=> -(1/2:ℝ)
-- refund fault. expose h Exp.L orientation
variable {z:I→ℕ}
variable (hQ:∀ᶠ i in l,(L i).b=0∧ Training (L i) (rink (x i)) ((F i).BasisT) (z i) ∧ 64*z i ≤d i) (hu:RateLE l (fate (Eve p)) (fun i=>Borealis.Galea.burst (Borealis.Galea.Gov s u) (z i)) (-(11/10)))
private lemma singleRefund {L : Host K T} {Y : Studio L} {w : Bid.Dir G L.c}
    {N : ChartRatio G} {sender : Sender L} {basis : Seats L.ForestQ}
    {s c e A u C rad fee cap : ℝ} {degree radius : ℕ}
    (center : Site L.f) (hN : LocalRatio N) (H : StackP N r R cap)
    (rich : L.Rich s c e A u C) (base : L.b = 0) (simple : G.Simple)
    (hs : 0 < s) (hc : 0 ≤ c) (he : 0 < e) (hA : 0 ≤ A)
    (scale : Scale Y rad) (bound : ‖w‖ ≤ rad) (stored : Stowed Y.X Y.ext)
    (locality : ReserveQ L center Y w radius) (trained : Training L center basis radius)
    (funded : Funded L basis sender fee degree) (q : Phase) :
    ‖(Y.inkY N (crestQ L sender Y)).seq q.val - (GPY L sender N w).seq q.val‖ ≤
      wallet3 G degree s c A u C rad (basis.card : ℝ) fee cap * burst (Gov s u) radius := by
  rw [ZVote L Y hN H rich he hs hc hA sender basis funded stored,
    tradeV hN L sender rich base simple w]
  exact refunds center hN H rich hs hc he hA scale bound locality le_rfl
    trained funded (Nat.cast_nonneg _) q

private lemma sourceWallet (G : Gauge) (degree : ℕ) (s c u C cap : ℝ)
    (L : Filter I) (rate A sizes counts fees : I → ℝ) (hr : Tendsto rate L atTop)
    (hA : RateLE L rate A 0) (hs : RateLE L rate sizes 0)
    (hn : RateLE L rate counts 0) (hf : RateLE L rate fees 0) :
    RateLE L rate (fun i => wallet3 G degree s c (A i) u C (sizes i) (counts i) (fees i) cap) 0 := by
  obtain ⟨bound, power, _, hbound⟩ := w45F G s c u C cap degree
  let g (p : ℝ) := RateLE.const p hr
  have hv : RateLE L rate (fun i => wealthV cap (A i)) 0 :=
    (g 1).add (hA.add (g _) hr |>.norm) hr
  exact RateLE.of_norm_le
    (((hv.mul (g bound)).mul (((g 1).add (hs.norm.add (hn.norm.add hf.norm hr) hr) hr).pow power hr)).mono
      (by norm_num)) (Eventually.of_forall fun i => hbound ..)

private lemma tokenRate {rate clock : I → ℝ} {exponent : ℝ}
    (L : Filter I) (U W : I → Token) (hr : Tendsto rate L atTop)
    (ht : RateLE L rate clock 0)
    (phase : ∀ q : Phase, RateLE L rate (fun i => (U i).seq q.val - (W i).seq q.val) exponent) :
    RateLE L rate (fun i => (U i).atK (clock i) - (W i).atK (clock i)) exponent := by
  apply (((phase 0).add ((ht.mul (phase 1)).mono (by simp)) hr).add
    (((ht.pow 2 hr).mul (phase 2)).mono (by simp)) hr).congr
  exact Eventually.of_forall fun i => gamma (U i) (W i) (clock i)
where
  gamma (x y : Token) (t : ℝ) :
      x.s - y.s + t * (x.l - y.l) + t^2 * (x.h - y.h) = x.atK t - y.atK t := by
    simp only [JetS.atK, smul_eq_mul]
    ring

private abbrev enrolledRefund (i : I)
    (base : (L i).b = 0 ∧ Training (L i) (rink (x i)) (F i).BasisT (z i) ∧ 64 * z i ≤ d i)
    (pledged : Viewer.Pledge (F i) (V i) (k + 6))
    (sector : Scale (fansU x p d n f i) (Ψs p v i) ∧ Stowed (Hpools x d i) (f i) ∧
      ∀ j ∉ (pond x p d n i).H, f i j = 0)
    (rich : (L i).Rich s c e (A i) u C' ∧ 0 ≤ A i) (q : Phase) :=
  singleRefund (L := L i) (Y := fansU x p d n f i) (w := (p i).w)
    (sender := (F i).scoreV (ψ i)) (basis := (F i).BasisT) (radius := z i) (degree := 9)
    (rink (x i)) hN H rich.1 base.1 hs hT hc he rich.2 sector.1 sector.1.w sector.2.1
    (Rootq (x i) (p i).w (f i) _ _ (z i) base.2.2) base.2.1
    (Viewer.vested (F i) (ψ i) pledged (by omega)) q

private abbrev localRead (i : I) : Token :=
  (p' i).inkY N (crestQ (L i) ((T!) i) (p' i))

private abbrev completeRead (i : I) : Token :=
  GPY (L i) ((T!) i) N (p i).w

private abbrev chargeAt (i : I) : ℝ :=
  wallet3 G 9 s c (A i) u C' (Ψs p v i) ((F i).BasisT.card : ℝ)
    (Crown.Ufee G (F i).k 0 ((F i).α (k+6) (ψ i) (V i))) s' * burst (Gov s u) (z i)

include hN H hs hT he hc hQ hF hb hS in
private lemma refundedPhase (q : Phase) : ∀ᶠ i in l,
    ‖(localRead (x := x) (p := p) (d := d) (n := n) (f := f) (F := F) (N := N) i).seq q.val -
      (completeRead (p := p) (F := F) (N := N) i).seq q.val‖ ≤
      chargeAt (p := p) (A := A) (V := V) (F := F) (z := z) (v := v) (k := k)
        (s := s) (c := c) (u := u) (C' := C') (s' := s') i := by
  filter_upwards [hQ, hF, hb, hS] with i hbase hpledge hsector hrich
  exact enrolledRefund (x := x) (v := v) (n := n) (hT := hT) (hc := hc) (he := he)
    (s' := s') (H := H) (hN := hN) (hs := hs) i hbase hpledge hsector hrich q

private lemma reportedCard (chase : Chase ζ l)
    (F : ∀ i, Viewer (L i)) (width : Lite ζ l (fun i => ((F i).k : ℝ)))
    (anchored : ∀ᶠ i in l, (F i).x = rink (x i)) :
    Lite ζ l (fun i => ((F i).BasisT.card : ℝ)) := by
  have hk : Lite ζ l (fun i => ((4*(F i).k : ℕ) : ℝ)) := by
    push_cast
    exact (Lite.flatC _ chase).rmul width
  apply (rO chase x hk).ofLe
  filter_upwards [anchored] with i hi
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro j hj
  apply mem_filter.mpr
  obtain ⟨term, hterm⟩ := (mem_filter.mp hj).2
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [hterm, ← hi]
  exact (mem_filter.mp term.property).2.1

include h hn ht hU hf hu in
private lemma totalExpense (ho : ∀ᶠ i in l, (F i).x = rink (x i)) :
    Wage ζ l (chargeAt (p := p) (A := A) (V := V) (F := F) (z := z) (v := v) (k := k)
      (s := s) (c := c) (u := u) (C' := C') (s' := s')) (-(11/10)) := by
       let tP := Ψs p v
       let a(i:I) := Crown.Ufee G (F i).k 0 ((F i).α (k+6) (ψ i) (V i))
       let Z := (9:ℕ)
       have hg : Wage ζ l a 0:= Crown.segue (fun i=>(F i).k) (hf.sound h) G h.tense hU 0; have he' : Wage ζ l tP 0:= (ΓΨ h hn v).sound h
       let Qf (i : I) := (F i).BasisT
       have hX : Lite ζ l (fun i => ((Qf i).card : ℝ)) := reportedCard x h F hf ho
       let θ(i:I):= ((Qf i).card:ℝ)
       have hsP := sourceWallet G Z s c u C' s' l (fate ζ) A tP θ a h.tense ht he' (hX.sound h) hg
       exact (hsP.mul hu).mono (by norm_num)

include hN H hs hT he hc hQ hF hb hS in
private lemma phaseDecay (q : Phase) (cost : Wage ζ l (chargeAt (p := p) (A := A) (V := V) (F := F) (z := z) (v := v) (k := k)
      (s := s) (c := c) (u := u) (C' := C') (s' := s')) (-(11/10))) :
    Wage ζ l (fun i =>
      (localRead (x := x) (p := p) (d := d) (n := n) (f := f) (F := F) (N := N) i).seq q.val -
      (completeRead (p := p) (F := F) (N := N) i).seq q.val) (-(11/10)) :=
  RateLE.of_norm_le cost (refundedPhase (x := x) (v := v) (n := n) (s' := s') (hN := hN) (H := H) (hs := hs) (hT := hT) (he := he)
    (hc := hc) (hQ := hQ) (hF := hF) (hb := hb) (hS := hS) q)

include h hn hT he hc hS hb hd hq ht hN H hs hQ hF hU hp hf hJ hz hu
noncomputable abbrev Rub (p:∀ i,Wall D E Q o η C m (L i))(F:∀ i,Viewer (L i))(N:ChartRatio G)(i:I):= (GPY (L i) ((F i).scoreV (Chase.σW (Eve p) i)) N (p i).w).atK (Chase.σW (Eve p) i)
set_option maxHeartbeats 200000
lemma Argo (ho:∀ᶠ i in l,(F i).x=rink (x i)):
 RateLE l (fate ζ) (fun i=> Rails (L i).P (p i).glare.V (L i).k (Hpools x d i) (pond x p d n i).H (WinK p t i) (J i) ((o') i)-Rub p F N i) (-(11/10)):=by
       have hh := Zpay h hn x v n hd hq hb hS hT he hc ht t s' H hN hs P' hp hf hF hU J hJ hz
       let U := localRead (x := x) (p := p) (d := d) (n := n) (f := f) (F := F) (N := N)
       let w := completeRead (p := p) (F := F) (N := N)
       have cost := totalExpense (x := x) (v := v) (c := c) (C' := C') (h := h) (hn := hn) (ht := ht) (hU := hU) (hf := hf) (hu := hu)
         (s' := s') ho
       have hG := fun q => phaseDecay (x := x) (v := v) (n := n) (s' := s') (hN := hN) (H := H) (hs := hs) (hT := hT) (he := he)
         (hc := hc) (hQ := hQ) (hF := hF) (hb := hb) (hS := hS) q cost
       have hp' := tokenRate l U w h.tense ((h.ζOpR.pays h.tense).mono (by norm_num)) hG
       apply RateLE.congr ((hh.mono (show -(3/2 : ℝ) ≤ -(11/10) by norm_num)).add hp' h.tense); exact Eventually.of_forall fun i=> sub_add_sub_cancel ..

end
end YM.OPE.Lass
