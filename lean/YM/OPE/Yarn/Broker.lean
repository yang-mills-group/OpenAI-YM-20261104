import YM.OPE.Yarn.Cabin
/-! # Between distinct event levels. Wear fixed arrangements up to that last step then remount. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
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
-- band: j to k descending from k. grant position send repeat
structure Band (C:Family G)(o:I→∀ i:ℕ, Site (C.side i p))(r:ℕ→ℕ)(j k m:ℕ) : Prop where
   clock i: j ≤ i→ i<k→∀ l,(C.path.levels.clock.op i p).ratio.parent (o l (i+1))=o l i
   crowd i: j ≤ i→ i<k→ Occupancy ((royal C m p i).place (fun l=>o l i)) (r i)
   skip i : j < i→ i<k→ let U:=(royal C m p i).place (fun l=>o l i); ∀ l k',l≠k'→ Loom.stride C 100 i-4≤ separation (U l) (U k')
variable (E: Band C o r j k m)(hm:m≤j)(hj:C.ref 0< j)
    (hF: j < k) (hn:k ≤ N)
    {Q:Config G (C.side k p)→ Marker.Poly (Names (Site (C.side m p)) I)}
    (ht:Wagon C N p m k (hm.trans hF.le) hn Q F d₀ (fun a=>o a k) (fun a=>Y a k) (fun a=> w a k))
    (hx:∀ a, Drive C.path j k N p (o a) (w a) D (Y a) hn) (hw:∀ a i,j ≤ i → i≤k → 0<w a i) (hV:∀ i,j < i→ i<k →∀ a,near C.path.levels i*w a i ≤ w a (i+1))
local notation "U'"=> gust C.path N p k Q
include H hm E ht hx hw hV hj
lemma run_car (hi:j < i)(hk:i ≤ k): Wagon C N p m i (hm.trans hi.le) (hk.trans hn) (gust C.path N p k Q i hk) F d₀ (fun a=>o a i) (fun a=>Y a i) (fun a=> w a i):=by
   refine ⟨ht.script.step,?_⟩; induction hk using Nat.decreasingInduction with
   | self=> rw [gust_base]; exact ht.fleet
   | of_succ i hi' IH=>
      rw [gust_step C.path N p k Q hi']; let e:=(T).clock.op i p; have ho : e.ratio.parent ∘ (fun a=>o a (i+1))=fun a=>o a i:=funext fun l=> E.clock i hi.le hi' l
      let x:V×I→ℝ:= (fun l=>w l (i+1)) ∘ Prod.snd
      rw [←ho]; refine Fleet.steady (D:=D) (w:=fun l=>w l (i+1)) («δ»:=renal C.path.levels) _ H.seed.wilson (hi'.trans_le hn) H.thor (hj.le.trans hi.le) (by rw [climbR (hm.trans hi.le)]; exact IH (hi.trans_le i.le_succ)) (by rw [show _ = _ from ho]; exact E.crowd _ hi.le hi') (fun j=>(hx j).drives i hi.le hi') (fun j=> hw j i hi.le hi'.le) ?_
      rw [show (C.path.levels.clock.op i p).ratio.parent ∘ _= _ from ho]; apply H.pebbles; exact fun j hj l=> hj ▸ hV i hi hi' l.snd; exacts [fun v=>hw v.snd _ (hi.le.trans i.le_succ) hi',fun v=>hw v.snd _ hi.le hi'.le,E.skip _ hi hi']
variable (b:ℕ) (L:Fibers I J) (q:J→Prop)
local notation "w*" => grouped C.path δ b l j (fun a=>w a (j+1)) L
local notation "d*"=> fineJob
lemma crux (hz:0<b)(hq:Fintype.card I ≤ b)(hψ:∀ i,q i→ L.Only i)
    (hΩ:∀ i:Site (C.side m p) × I, let x' := (royal C m p j).place (fun l=>o l j); coverNumber (C.path.levels.budget j).B ({x' (i.1,L.twig (L.bunch i.2)),x' i}:Support _) ≤ l): ∃ P':J→ Lamp G (C.side j p),
    (∀ i,q i→ P' i=Y (L.twig i) j)∧ (∀ i,¬ q i→(P' i).Flex (R j) (o (L.twig i) j) (4*(1/w* i))) ∧
    Wagon C N p m j hm (hF.le.trans hn) (fun U=>Fibers.reap (partialGroup V L) (gust C.path N p k Q j hF.le U)) (fun i=>fineJob F (L.contents i)) (d₀.image L.bunch) (fun i=>o (L.twig i) j) P' (w*):=by
    let e:= (T).clock.op j p; have he : e.ratio.parent ∘ (fun a=>o a (j+1))=fun a=>o a j:= funext fun i=>E.clock j le_rfl hF i
    obtain ⟨P',ha,hM,hT⟩:= Fleet.collect (w:=fun i=>w i (j+1)) («P»:=Z j) (o:=fun a=>o a (j+1)) (N:=N) («δ»:=renal C.path.levels) (fun i=> Y i j) H.seed.wilson (hF.trans_le hn) H.thor hj.le ((climbR (C:=C) (p:=p) hm).symm ▸ (run_car H E hm hj hF hn ht hx hw hV j.lt_succ_self hF).fleet) (he.symm ▸ E.crowd _ le_rfl hF) (fun i=>(hx i).drives j le_rfl hF) b l L q hψ (H.strong hj (hF.le.trans hn)) (H.mantle hj.le) hz hq (by rw [he]; exact hΩ)
    rw [he] at hM hT; rw [gust_step C.path N p k Q hF]; refine ⟨P',ha,hM,?_, hT⟩; rw [← gust_step C.path N p k Q hF]; exact Wagon.regroups L (ht.script.step)
end YM.OPE.Yarn

