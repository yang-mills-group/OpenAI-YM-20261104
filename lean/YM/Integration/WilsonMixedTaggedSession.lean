import YM.Integration.WilsonMixedTaggedCourse
import YM.Integration.WilsonMixedTaggedOutput

/-! One funded original lower course produces both original physical programs and
jointly small differences of their restored H and K. The number of colors
is arbitrary and no affine identity for mixed arrays is required. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedTaggedSession
open Finset Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Topology BigOperators Classical

private theorem same {G:Gauge} {C:Family G} {n b m N p:ℕ} {V:ℕ → Type}
    [∀i,DecidableEq (V i)] [∀i,Fintype (V i)] {W:Type*} (A:Planner C p n V W)
    {H:∀i,Census (V i)} (s:W → ℕ) {hb:n ≤ b}
    {F F':∀i,Config G (C.side i p) → Poly (H i)}
    (f:Replay A s hb m F N) (f':Replay A s hb m F' N) (top:F m=F' m)
    {j:ℕ} (bj:b ≤ j) (jm:j ≤ m) : F j=F' j := by
  induction jm using Nat.decreasingInduction with
  | self=>exact top
  | of_succ i im ih=>
    obtain ⟨_,l⟩:=f.downhill i bj im
    obtain ⟨_,r⟩:=f'.downhill i bj im
    rw [l,r,ih (bj.trans i.le_succ)]

private theorem field_rows {G:Gauge}{n:Side}{V:Type}[DecidableEq V][Fintype V]{B:Census V}
    {R:Rep G n}{o:V → Site n}{w:V → ℝ}{e:ℝ}{P:V → Three G n}
    {X:Config G n → Poly (census B)}
    (b:MenuBoard R (liveRow P) X (o ∘ Prod.fst) (w ∘ Prod.fst) e 1) :
    Served R (liveRow (fun v=>(P v).2.1)) (liveRow (fun v=>profile R.activities (P v).2.2))
      X (o ∘ Prod.fst) (w ∘ Prod.fst) e 1 := by
  have reg : (fun v=>(liveRow P v).2.1) = liveRow (fun v=>(P v).2.1) := by
    funext ⟨v,bit⟩
    cases bit <;> rfl
  have forced : (fun v=>profile R.activities (liveRow P v).2.2) =
      liveRow (fun v=>profile R.activities (P v).2.2) := by
    funext ⟨v,bit⟩
    cases bit
    · rfl
    · funext p U
      simp [liveRow,profile,cram]
  simpa only [reg,forced] using b.grants

def Matched {G:Gauge}{n:Side}{V:Type}[DecidableEq V][Fintype V]{B:Census V}
    (R:Rep G n)(P:V → Three G n)(o:V → Site n)(w:V → ℝ)(e cash:ℝ)
    (F L:Config G n → Poly B) : Prop :=
    ∃ (H₁ H₀:Support n → Config G n → Poly B) (K₁ K₀:Box n → Config G n → Poly B),
      Carton o H₁ K₁ R.p.threshold ∧ Carton o H₀ K₀ R.p.threshold ∧
      F=restore R (fun v=>(P v).2.1) (fun v=>profile R.activities (P v).2.2) H₁ K₁ ∧
      L=
        restore R (fun v=>(P v).2.1) (fun v=>profile R.activities (P v).2.2) H₀ K₀ ∧
      Towed w id (fun a U=>H₁ a U-H₀ a U) R.p.B e cash ∧
      Towed w Prod.fst (fun a U=>K₁ a U-K₀ a U) R.p.B e cash

private theorem paired {G:Gauge}{n:Side}{V:Type}[DecidableEq V][Fintype V]{B:Census V}
    {R:Rep G n}{o:V → Site n}{w:V → ℝ}{e:ℝ} (P:V → Three G n)
    {X:Config G n → Poly (census B)} {F:Config G n → Poly B} {z:ℂ} (small:‖z‖ ≤ 1)
    (wp:∀v,0 < w v)
    (funded:MenuBoard R (liveRow P) X (o ∘ Prod.fst) (w ∘ Prod.fst) e 1)
    (eq:F=fun U=>specialize B z (X U)) :
    Matched R P o w e ‖z‖ F (fun U=>specialize B 0 (X U)) := by
  obtain ⟨H,K,bill,regular,forced⟩:=WilsonMixedTaggedOutput.original small
    (fun v=>(P v).2.1) (fun v=>profile R.activities (P v).2.2) wp (field_rows funded)
  exact ⟨H z,H 0,K z,K 0,(bill z).1,(bill 0).1,eq.trans (funext (bill z).2),
    funext (bill 0).2,regular,forced⟩

variable {G:Gauge} {C:Family G} {n b m N p d k:ℕ} {V:ℕ → Type}
variable [∀i,DecidableEq (V i)] [∀i,Fintype (V i)] {W:Type*}
variable (A:Planner C p n V W) (H:∀i,Census (V i)) (s:W → ℕ) (I:∀i,V i → Body)
variable (h:C.Makes) {D:Address.Rail C} (storage:Storage C D) {q f:ℕ → ℝ} {T:Pens C p W}
local notation "rep" => C.path.rep N p
local notation "rows" => imprint h A I T
local notation "rads" => west C q f k
local notation "expo" => fun i:ℕ=>if i=m then (C.path.levels.budget i).supportExponent-4
  else (C.path.levels.budget i).supportExponent
local notation "fields" => (i:ℕ) → Config G (C.side i p) → Poly (H i)
local notation "tagged" => fun i=>census (H i)

private theorem rolls (hb:n ≤ b) (bm:b ≤ m) (mn:m ≤ N)
    {F:fields} (run:Replay (H:=H) A s hb m F N) (X:Config G (C.side m p) → Poly (census (H m)))
    (intX:Integrable X (prior G _)) :
    ∃ Z:(i:ℕ) → Config G (C.side i p) → Poly (census (H i)),
      Replay (H:=tagged) (planner A) s hb m Z N ∧ Z m=X ∧
      ∀u:ℂ,Replay (H:=H) A s hb m (fun i U=>specialize (H i) u (Z i U)) N := by
  let license (i:ℕ) (bi:b ≤ i) (im:i < m):=(run.downhill i bi im).choose
  obtain ⟨Z,replayed,head⟩:=reels_write (planner A) s hb bm (H:=tagged)
    (fun i bi im=>step_license A (license i bi im)) X N
  refine ⟨Z,replayed,head,?_⟩
  intro u
  exact WilsonMixedTaggedCourse.replay A s u mn license replayed (head.symm ▸ intX)

include storage in
private theorem lower_bank (hb:n ≤ b) (mn:m ≤ N)
    (purse:Purse C f q b m d k) (route:Toured (planner A) tagged hb m f k)
    (lamp:Lantern s h (p:=p) (b:=b) (D:=D) m N q T)
    {Z:(i:ℕ) → Config G (C.side i p) → Poly (census (H i))} (replayed:Replay (H:=tagged) (planner A) s hb m Z N)
    (rank:∀v,s v ≤ d) (prep:PreparedA A I b m hb)
    (cap:∀v:V b,Cap (s (A.labelY b v)+2) (I b v) 1)
    {e:ℝ} (width:(C.path.levels.budget m).supportExponent-4 ≤ e)
    (base:MenuBoard (R:=census (H m)) (rep m) (liveRow (rows m mn)) (Z m) (A.supportX m ∘ Prod.fst)
      (fun _=>rads m) e 1) :
    ∀j:ℕ,b ≤ j → ∀jm:j ≤ m,MenuBoard (rep j) (liveRow (rows j (jm.trans mn))) (Z j)
      (A.supportX j ∘ Prod.fst) (fun _=>rads j) (expo j) 1 := by
  have imps j (jN:j ≤ N):imprint h (planner A) (bodies I) T j jN=liveRow (rows j jN) :=
    funext (body_imprint A I T h jN)
  have initial : MenuBoard (rep m) (imprint h (planner A) (bodies I) T m mn) (Z m)
      ((planner A).supportX m) (fun _=>rads m) e 1 := by
    rw [imps]
    exact base
  have bank:=session (planner A) (H:=tagged) s (bodies I) h storage hb mn T purse route lamp
    replayed rank (prepared A prep) (caps A cap) width initial
  intro j bj jm
  rw [←imps]
  exact bank j bj jm

private theorem identify {hb:n ≤ b} {F:fields} {Z:(i:ℕ) → Config G (C.side i p) → Poly (census (H i))}
    {X:Config G (C.side m p) → Poly (census (H m))} {z:ℂ}
    (run:Replay (H:=H) A s hb m F N)
    (film:Replay (H:=H) A s hb m (fun i U=>specialize (H i) z (Z i U)) N)
    (top:F m=fun U=>specialize (H m) z (X U)) (head:Z m=X)
    {j:ℕ} (bj:b ≤ j) (jm:j ≤ m) : F j=fun U=>specialize (H j) z (Z j U) := by
  have start : F m=fun U=>specialize (H m) z (Z m U) :=
    top.trans (congrArg (fun T:Config G (C.side m p) → Poly (census (H m))=>
      fun U=>specialize (H m) z (T U)) head.symm)
  exact same (H:=H) (F:=F) (F':=fun i U=>specialize (H i) z (Z i U)) A s run film start bj jm

include storage in
theorem original (hb:n ≤ b) (bm:b ≤ m) (mn:m ≤ N)
    (purse:Purse C f q b m d k) (route:Toured (planner A) tagged hb m f k)
    (lamp:Lantern s h (p:=p) (b:=b) (D:=D) m N q T)
    {F:fields} (run:Replay (H:=H) A s hb m F N) (rank:∀v,s v ≤ d) (prep:PreparedA A I b m hb)
    (cap:∀v:V b,Cap (s (A.labelY b v)+2) (I b v) 1)
    {e:ℝ} (width:(C.path.levels.budget m).supportExponent-4 ≤ e)
    {X:Config G (C.side m p) → Poly (census (H m))}
    (base:MenuBoard (R:=census (H m)) (rep m) (liveRow (rows m mn)) X (A.supportX m ∘ Prod.fst)
      (fun _=>rads m) e 1) {z:ℂ} (small:‖z‖ ≤ 1)
    (top:F m=fun U=>specialize (H m) z (X U)) :
    ∃ L:fields, Replay (H:=H) A s hb m L N ∧ L m=(fun U=>specialize (H m) 0 (X U)) ∧ 
      ∀j:ℕ,b ≤ j → ∀jm:j ≤ m,Matched (B:=H j) (rep j) (rows j (jm.trans mn))
        (A.supportX j) (fun _=>rads j) (expo j) ‖z‖ (F j) (L j) := by
  obtain ⟨Z,replayed,head,replayed'⟩:=rolls A H s hb bm mn run X base.cleared
  have bank:=lower_bank (T:=T) (N:=N) (m:=m) (q:=q) (f:=f) (d:=d) (k:=k) A H s I h storage hb mn purse route lamp replayed rank prep cap width
    (head.symm ▸ base)
  refine ⟨fun i U=>specialize (H i) 0 (Z i U),replayed' 0,?_,?_⟩
  · exact congrArg (fun F=>fun U=>specialize (H m) 0 (F U)) head
  intro j bj jm
  have paid:=bank j bj jm
  have wp:0 < rads j := mul_pos (purse.upper j bj jm).1 (grantw (purse.headV j bj jm))
  have prev:=identify (F:=F) (Z:=Z) (X:=X) (z:=z) A H s run (replayed' z) top head bj jm
  exact paired (B:=H j) (R:=rep j) (o:=A.supportX j) (w:=fun _=>rads j)
    (rows j (jm.trans mn)) small (fun _=>wp) paid prev

end YM.Integration.WilsonMixedTaggedSession
