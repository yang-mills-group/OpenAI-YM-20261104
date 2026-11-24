import YM.OPE.Strobe.Flare
import YM.OPE.Strobe.Innings
import YM.OPE.Loom.Money
/-! # After the measurements are prescribed: earn, then long-coast. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
variable {F:I→ Config G (C.side N p)→ℂ}{o:I→ ∀ i:ℕ, Site (C.side i p)}{w:I→ℕ→ℝ} {d₀:Finset I}{Y:I→∀ i:ℕ,Lamp G (C.side i p)}
local notation "Z" => royal C m p
local notation "r*" => stepUp
def rod (i₀:I) : Fibers I Unit:=⟨fun _=>(),fun _=>i₀,fun _=>rfl⟩
section
lemma rose (i:I)(X:Unit): (rod i).contents X=Finset.univ:=by ext j; rw [Fibers.focuses]; simp [rod]
end
-- displays.Full.Never compare with collection of runners from different mesh
variable {w:I→ℝ} -- ag shadow notation!
local notation "x*" => ((Z j).place (fun a=>o a j))
local notation "v!" => Vac.treasury
structure Shown (C:Family G)(N p m k:ℕ)(F:I→ Config G (C.side N p)→ℂ)(o:I→ Site (C.side k p))(w:I→ℝ):Prop where
   admits : ∃ Q X, ShowF C N p m k Q F o w X ∧ ∀ i,(X i).Flex (C.path.rep N p k) (o i) (4*(1/w i))
include H
variable (b:ℕ) (i₀:I)(E:Band C o r j k m)
local notation "t*" => card (Finset.univ : Finset I)
def shade (C:Family G)(b l j k:ℕ)(long:Bool)(w:I→ℝ):= cashIn C.path (renal C.path.levels) b l j (fun i=> Yarn.fee C j k long*w i)
include E
lemma cored (long:Bool)(hl:long=true→∀ i,∀ a,j ≤ a→ a<k → o i (a+1)= (C.path.levels.clock.op a p).ratio.embed (o i a)) (hx:C.ref 0<j) (hz:j<k)(hm:m≤j)(hn:k ≤ N)(hS:Shown C N p m k F (fun a=>o a k) w)(he:t* ≤ b) (hO:∀ i:V × I, coverNumber (C.path.levels.budget j).B ({x* (i.1,i₀),x* i}:Support _) ≤ l) : Shown C N p m j (fun _:Unit=>fineJob F univ) (fun _=>o i₀ j) (fun _=> shade C b l j k long w):=by
    obtain ⟨Q,X,hQ,hX⟩:= hS.admits; let L:=rod i₀; let Y':= Yarn.fee C j k long; have hp:= hQ.fleet.secure; have hh:= Yarn.voucher H hz long; choose S hT hZ using fun i=> Yarn.ripe H _ (fun i hi hk=> E.clock i hi hk _) hz hx.le hn (hp i) (hX i) long (fun h=> hl h i)
    let w'(a:I) (_:ℕ):= Y'*w a; have hr(i):0<Y'*w i:=mul_pos hh.1 (hp i); let hQ':= hQ.fleet.shrink hr (fun i=>mul_le_of_le_one_left (hp i|>.le) hh.2); have hs: ShowF C N p m k Q F (fun a=>o a k) (fun i=>w' i k) (fun i=> S i k):=by simp_rw [hT]; exact ⟨hQ.sings,hQ'⟩
    letI:Nonempty I:= ⟨i₀⟩; rw [card_univ] at he; obtain ⟨P',ha,hM,hA⟩:= ShowF.bonded H E hm hx hz hn hs hZ (fun a i _ _=>hr a) (fun i _ _ a=>mul_le_of_le_one_left (hr a|>.le) ((inv_le_one₀ (zero_lt_one.trans ((T).fits.delayed (i+1)))).mpr ((T).fits.delayed _|>.le))) b L (fun i=> False) (Fintype.card_pos.trans_le he) he (by simp) hO
    have ht(i): L.contents i=(univ:Finset I) := rose _ _; unfold grouped at *; simp_rw [ht] at *; exact ⟨_,P',hA,fun i=>hM i (fun h=>h)⟩ -- multi existential via Show.intro fields? refine
omit E H in
lemma atone {Q: Config G n→ℂ} (A:Tiling n) (β : ℝ) (hv: Seam G n β)(hp:Interior (A.chamber 0) Q) : ‖moment β Q‖ ≤ A.rootTest β Q:=by
    simpa only [Fintype.prod_unique,Tiling.copy_zero] using A.planted hv (fun _:Unit=> (0:A.Cell)) (injective_of_subsingleton _) (fun _=>Q) (fun _=>hp) -- typo eta
-- OUTPUT with fixed stop.Cost. long aligned.Any Stitch use.
local notation "xo!" => (fun i=>(0:Site (C.side i p)))
local notation "x*!" => (fun _:Unit=>xo!)
local notation "y*" => (shade C b l j k false w)
def pound (C:Family G)(b m z j k l:ℕ)(w:I→ℝ):= earns C m z / shade C 1 1 z j true (fun _:Unit=>shade C b l j k false w)
set_option maxHeartbeats 200000 in
lemma shoring (b:ℕ) (E':Band C (p:=p) (fun _:Unit=>fun i=>(0:Site (C.side i p))) r z j m)(hl:C.ref 0<z)(ht:z<j)(hz:j<k)(hm:m≤ z)(hn:k ≤ N)(he:o i₀= xo!)(hS:Shown C N p m k F (fun a=>o a k) w)(hF:Fintype.card I ≤ b)(hA:∀ i:V × I, coverNumber (C.path.levels.budget j).B ({x* (i.1,i₀),x* i}:Support _) ≤ l): (center C.S p (hm.trans (ht.le.trans (hz.le.trans hn))) 0).rootTest (C.beta N p) (fineJob F univ) ≤ pound C b m z j k l w:=by
    have hX:= cored H b i₀ E false (by simp) (hl.trans ht) hz (hm.trans ht.le) hn hS (by simpa using hF) hA; rw [he] at hX; obtain ⟨Q,X,hQ,hP⟩:= (cored (o:= fun _:Unit=>xo!) H 1 () E' true (fun _ _ _ _ _=>embed_origin .. |>.symm) hl ht hm (hz.le.trans hn) hX (by simp) (l:=1) (by intro i; let y i:= (Z z).place (fun _:Unit=>(0:Site (C.side z p))) i; change coverNumber _ {y _,y i} ≤1; rw [show y (i.1,())=y i from rfl]; exact Loom.assembled _ _ (p:=0) (by simp [separation_self]))).admits -- check outside parentheses annotation
    let f:= (fun _:Unit=>fineJob F univ); have h': fineJob f univ=fineJob F univ:=by unfold fineJob;funext i;rw [Fintype.prod_unique];rfl
    have hf:= spiking H hm hl.le (ht.le.trans (hz.le.trans hn)) hQ (hP ()); change (Cells.center C.S p (hm.trans (ht.le.trans (hz.le.trans hn))) 0).rootTest _ (fineJob f univ) ≤ _ at hf; rw [h'] at hf; unfold pound; exact hf
end YM.OPE.Strobe

