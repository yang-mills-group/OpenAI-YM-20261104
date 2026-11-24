import YM.OPE.Compatible.Cant.Snow
/-!
# Transport of pairings modulo the residual submodules

`YM.OPE.Stroke.commuting` compares flag representatives before and after a transport satisfying `Ace` when their discrepancies lie in the respective `Sapling` submodules.
At pinned sites on an even lattice satisfying the barrier bound, the source pairing at order `k + r` equals the target pairing at order `k`.
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
-- Changing either argument by a residual gives a Thick difference of phase pairings.
variable (t:Even n.val)(x y:Site n)(hk:Pins K P x y)
include hk
lemma PhaseV (i':M)(u v q r':F!)(he:u-v∈ Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀) i')(ht:q-r'∈ Sγ i')(l':Phase):
    let f(k:ℕ):=PhaseP (H:=H) (hs:=hs) (D₀:=D₀) (V i') hp (zero_le_one.trans (hq i')) a x y t l' k
    Thick (μ l*(μ l)) (fun i=>f i u q-f i v r'):=by
       let Z:=Fallix G D₀.aware K (V i'|>.gear) hp; let p(z:ℕ):= Variance.HillP (V i') H hp hs (zero_le_one.trans (hq i')) P x y t a l' z (τ:=τ) (d:=d); have hg(w z:F!)(h:w-z∈ Sγ i')(q:F!) : Thick (μ l*(μ l)) (fun i=>p i (Z w-Z z) (Z q)) ∧ Thick (μ l*(μ l)) (fun i=> p i (Z q) (Z w-Z z)):=by
           have he : Z (w-z)∈ Variance.SailSap (V i') H hp hs (zero_le_one.trans (hq i')) P a l := h; rw [Z.map_sub] at he; exact Variance.quakeX (V i') H hp hs (zero_le_one.trans (hq i')) P x y t (Z w-Z z) a he hk _ l'
       exact naryT (hg _ _ he q).1 (hg _ _ ht v).2 -- Combine the contributions from the two arguments.
-- Compare the source and target pairings at orders differing by r.
variable {ht:4 ≤ j}{hz:1≤uα}{U':Z.Ω I uα}
variable (he: Z.Floss A U' ht (le_trans zero_le_one hz) k Hp a)(f':Tracts G d τ→L[ℝ] Tracts G d τ) (i':M)(j':I)
local notation "AC"=> Ace D₀ H hs a (V i') (A j') (zero_le_one.trans (hq i')) (zero_le_one.trans (hz j')) hp ht r f'
local notation "CΓ"=>Sapling (V:=A) (H:=H) (hs:=hs) (hq:=hz) (hp:=ht) (a:=a) (D₀:=D₀) j'
include hX he
set_option maxHeartbeats 200000 in
lemma commuting (e:J!)(hb:barrier P≤ n.val)(l':Phase)(L:AC)(v v':F!)(p q:U.flag e.val i')(u w: U'.flag e.val j')
    (hu:v-p.val∈ Sγ i')(hv:v'-q.val∈ Sγ i')(hy:f' v-u.val∈ CΓ)(hQ:f' v'-w.val∈ CΓ)(k:ℕ):
      Por Hp Z e.val l' t x y a (k+r) (U.read e.val e.isLt i' p) (U.read e.val e.isLt i' q)= Por Hp Z e.val l' t x y a k (U'.read e.val e.isLt j' u) (U'.read e.val e.isLt j' w):=by
       let ha(j:ℕ):=PhaseP (H:=H) (hs:=hs) (D₀:=D₀) (V i') hp (zero_le_one.trans (hq i')) a x y t l' j; let ha'(j:ℕ):=PhaseP (H:=H) (hs:=hs) (D₀:=D₀) (A j') ht (zero_le_one.trans (hz j')) a x y t l' j; let y₁:=fun i=>ha (i+r) v v'; let y₂:=fun i=>ha (i+r) p.val q.val; let y₃:=fun i=> ha' i (f' v) (f' v'); let y₄:=fun i=>ha' i u.val w.val
       have hp : μ l≤μ e.val:=by by_cases h:l=e.val; exact (congr_arg (lapPrice P.L) h)|>.le; exact (stairPrice _ e.val l (by omega) P.coarse).le
       have hx:=mul_le_mul hp hp (EndFare P.L l|>.le) (EndFare P.L e.val|>.le)
       let N:=U.read _ e.isLt i'; let N':=U'.read _ e.isLt j'; have hc : Thick (μ l*(μ l)) (y₁-y₂):=parkF r (PhaseV (hq:=hq) (D₀:=D₀) (V:=V) (H:=H) a t x y hk i' _ _ _ _ hu hv l') -- Shift the source residual estimate by r.
       have hh : Thick (μ l*(μ l)) (y₃-y₄):= PhaseV (hq:=hz) (D₀:=D₀) (V:=A) (H:=H) a t x y hk j' _ _ _ _ hy hQ l'
       exact congr_fun (onset (EpSky Hp Z a t x y l' (N p) (N q) r) (EpSky Hp Z a t x y l' (N' u) (N' w) 0) (hc.extend hx) (hh.extend hx) ((L.travel n t x y hb hk l' v v').extend hx) (he.corn e.val e.isLt l' n t x y hb hk j' u w) (parkF r (hX.corn e.val e.isLt l' n t x y hb hk i' p q))) k
end
end YM.OPE.Stroke
