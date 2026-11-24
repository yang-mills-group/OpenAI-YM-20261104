import YM.OPE.Compatible.Cant.Rose
/-!
# Transport through the flag filtration

`YM.OPE.Stroke.poet` proves `Carries` at each depth `e ≤ l + 1` for the given source and target readouts and compatible transport.
In the induction step, vanishing of all admissible pairings in both arguments places the target readout in `Dross`, which permits passage to the next flag.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
variable {uα:I→ℝ}{A:(v:I)→Alps K T j (uα v)}
local notation "μ"=>lapPrice (Patch.L P)
section
variable (hX: Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)
variable {ht:4 ≤ j}{hz:1≤uα}{U':Z.Ω I uα}
variable (he: Z.Floss A U' ht (le_trans zero_le_one hz) k Hp a)(f':Tracts G d τ→L[ℝ] Tracts G d τ) (i':M)(j':I)
local notation "AC"=> Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f'
local notation "CΓ"=>Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) j'
variable (h':∀ i,(A i).clip=p')(hv:l*l≤ τ 0)(L:Lance X)(T₀: Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f')
local notation "Vγ" e:max v:max => InVivid (U:=U) (U':=U') (hz:=hz) (A:=A) (ht:=ht) Z a f' i' j' e v
local notation "Cρ"=> Carries (hp:=hp) (ht:=ht) (hq:=hq) (V:=V) (A:=A) (hz:=hz) Z a f' U U' i' j'
private lemma equalPairZeros {E : Type*} (p : E) (B C : E → E → ℝ)
    (eq : ∀ x y, B x y = C x y) (zero : ∀ q, B p q = 0 ∧ B q p = 0) :
    ∀ q, C p q = 0 ∧ C q p = 0 :=
  fun q => ⟨(eq p q).symm.trans (zero q).1, (eq q p).symm.trans (zero q).2⟩

private lemma vanishingPairIsDross (e : J!) (w : Mint Z e.val)
    (cancel : ∀ (q : Mint Z e.val) (n : Side) (t : Even n.val) (x y : Site n),
      barrier P ≤ n.val → Pins K P x y → ∀ (s : Phase) (k : ℕ),
        Por Hp Z e.val s t x y a k w q = 0 ∧ Por Hp Z e.val s t x y a k q w = 0) :
    w ∈ Dross Hp Z a e.val := by
  change Kneel Hp Z a w
  intro n t x y size pin k s
  exact equalPairZeros w (Por Hp Z e.val s t x y a k)
    (fun u v => UnitBorn Hp Z a t x y s k u v) (fun u v => flareP Hp Z a u v t x y s k)
    (fun q => cancel q n t x y size pin s k)

include hX he h' hv L T₀
set_option maxHeartbeats 200000 in
lemma poet {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (C:Bals Hp Z a A' κ)(e:ℕ)(hx:e ≤ l+1): Cρ e:=by
       induction e with
       | zero=> intro u hu; rw[Bay,U'.first,top_sup_eq]; exact Submodule.mem_top
       | succ e ih=>
          intro p h; let E:Fin (l+1):=⟨e,hx⟩; have he':= ih (Nat.le_trans (Nat.le_succ _) hx); obtain ⟨x,hS,y,hy,hx'⟩:= Submodule.mem_sup.mp h; let u:U.flag e i':=⟨x,U.moves e i' hx hS⟩; obtain ⟨v,hv',z,hz',hL⟩:= Submodule.mem_sup.mp (he' p ((sup_le_sup_right (U.moves e i' hx) (Sγ i')) h)); let u':U'.flag e j':=⟨v,hv'⟩; let w:=U'.read e hx j' u'; have hA:p-u.val∈ Sγ i':=by change p-x∈ Sγ i';rw [← hx',add_sub_cancel_left]; exact hy -- The first decomposition gives the source residual.
          have hB:f' p-u'.val∈ CΓ:=by change f' p-v∈ CΓ;rw[← hL,add_sub_cancel_left];exact hz'
          have hh:= (U.depth e i' hx u).1 hS; have ht' : w ∈ Dross Hp Z a e :=
            vanishingPairIsDross Hp Z a E w
              (portraitK (hq:=hq) (hz:=hz) Hp Z a hX he f' i' j' h' hv L T₀ C E he' p u u' hA hB hh)
          let S:= fun i=> Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) i; have he: u'.val∈ Bay U'.flag S (e+1) j':= (Reef (hq:=hz) Hp Z a U' h' he C hv L E j' u').1 ((C.tricks E|>.hero _).1 ht'); rw [← hL]; exact Submodule.add_mem _ he (le_sup_right (a:=U'.flag (e+1) j') hz')
end
end YM.OPE.Stroke
