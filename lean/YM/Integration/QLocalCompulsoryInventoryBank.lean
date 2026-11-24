import YM.Integration.QLocalCompulsoryInventoryProduct
import YM.Integration.WilsonLimitConstruction.FundedMarkedFieldSplit
import YM.Overlay.Pays

/-! Each old submitted compulsory entry keeps its address through a fixed
injection. The other finitely many seats store the genuine signed
coefficients of the increment on the same forced row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalCompulsoryInventoryBank
open Function Finset Lattice Wilson RG Marker Overlay Extra.Trajectories
open RG3.Script.Picnic LocalComparison QLocalCompulsoryInventoryProduct
open WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V X:Type} [DecidableEq V] [Fintype V] {Γ:Census V}
    {P:Rep G n} {o:V→Site n}

def roster (Γ:Census V) : (ℕ⊕Γ.Mode)≃ℕ :=
  @Denumerable.eqv _ (Classical.choice (nonempty_denumerable _))

def extra (a:Bands Γ P) (h:Site n→ Config G n→Poly Γ) (i:ℕ) (U:Config G n) :=
  (Poly.pass (localCharge P h i U)-1)*a.each i U

theorem extra_quiet (a:Bands Γ P) (h:Site n→ Config G n→Poly Γ) (hz:∀ξ U,(h ξ U).part Γ.quiet=0)
    (i:ℕ) (U:Config G n) : (extra a h i U).part Γ.quiet=0 := by
  simp [extra,Poly.pass_part _ (local_quiet h hz i U)]

def mode (old:ℕ→ℕ→Γ.Mode) (i j:ℕ) : Γ.Mode :=
  Sum.elim (old i) (fun s=>if s=Γ.quiet then old i 0 else s) ((roster Γ).symm j)

def entry (a:Bands Γ P) (h:Site n→ Config G n→Poly Γ) (i j:ℕ) (U:Config G n) : ℂ :=
  Sum.elim (fun k=>a.entries i k U) (fun s=>if s=Γ.quiet then 0 else (extra a h i U).part s)
    ((roster Γ).symm j)

def tape (T:Taste X o P Γ) (h:X→Site n→ Config G n→Poly Γ) : Compulsory X Γ G n :=
  ⟨mode T.menu.marks,fun x=>entry (T.menu.terms x) (h x)⟩

def bands (a:Bands Γ P) (h:Site n→ Config G n→Poly Γ) : Bands Γ P :=
  {a with marks:=mode a.marks,entries:=entry a h}

theorem terms (T:Taste X o P Γ) (h:X→Site n→ Config G n→Poly Γ) (x:X) :
    (replace T (tape T h)).menu.terms x=bands (T.menu.terms x) (h x) := rfl

theorem original (T:Taste X o P Γ) (h:X→Site n→ Config G n→Poly Γ) (i j:ℕ) (x:X) (U:Config G n) :
    (tape T h).mode i (roster Γ (.inl j))=T.menu.marks i j ∧
      (tape T h).value x i (roster Γ (.inl j)) U=T.menu.force x i j U := by
  simp [tape,mode,entry]
  rfl

theorem mixed (T:Taste X o P Γ) (h:X→Site n→ Config G n→Poly Γ) (i:ℕ) (s:Γ.Mode)
    (hs:s≠Γ.quiet) (x:X) (U:Config G n) :
    (tape T h).mode i (roster Γ (.inr s))=s ∧
      (tape T h).value x i (roster Γ (.inr s)) U=(extra (T.menu.terms x) (h x) i U).part s := by
  simp [tape,mode,entry,hs]

theorem each (T:Taste X o P Γ) (h:X→Site n→ Config G n→Poly Γ)
    (hz:∀x ξ U,(h x ξ U).part Γ.quiet=0) (x:X) (i:ℕ) (U:Config G n)
    (H:Summable (fun j=>(T.menu.terms x).tagged i j U)) :
    ((replace T (tape T h)).menu.terms x).each i U=changed (T.menu.terms x) (h x) i U := by
  let a:=T.menu.terms x
  let b:=(replace T (tape T h)).menu.terms x
  let D:=extra a (h x) i U
  let f:ℕ⊕Γ.Mode→Poly Γ:=Sum.elim (fun j=>a.tagged i j U) (fun s=>Poly.send s (D.part s))
  have seat (v:ℕ⊕Γ.Mode):b.tagged i (roster Γ v) U=f v:=by
    cases v with
    | inl j=>
      change Poly.send ((tape T h).mode i _) ((tape T h).value x i _ U)=a.tagged i j U
      rw [(original T h i j x U).1,(original T h i j x U).2]
      rfl
    | inr s=>
      by_cases hs:s=Γ.quiet
      · subst s
        change Poly.send ((tape T h).mode i _) ((tape T h).value x i _ U)=Poly.send Γ.quiet (D.part Γ.quiet)
        have hD:D.part Γ.quiet=0:=extra_quiet a (h x) (hz x) i U
        simp [tape,entry,D,hD]
      · change Poly.send ((tape T h).mode i _) ((tape T h).value x i _ U)=Poly.send s (D.part s)
        rw [(mixed T h i s hs x U).1,(mixed T h i s hs x U).2]
  have finite:HasSum (fun s=>Poly.send s (D.part s)) D:=by
    simpa only [Poly.studs] using hasSum_fintype (fun s=>Poly.send s (D.part s))
  have joined:HasSum f ((∑' j,a.tagged i j U)+D):=HasSum.sum (f:=f) H.hasSum finite
  have add:(∑' j,b.tagged i j U)=(∑' j,a.tagged i j U)+D:=
    ((roster Γ).tsum_eq _).symm.trans ((tsum_congr seat).trans joined.tsum_eq)
  change Poly.send Γ.quiet (P.activities.K i U:ℂ)+(∑' j,b.tagged i j U)=
    Poly.pass (localCharge P (h x) i U)*a.each i U
  rw [add,←add_assoc]
  change a.each i U+(Poly.pass (localCharge P (h x) i U)-1)*a.each i U=_
  ring

theorem funded (T:Taste X o P Γ) (h:X→Site n→ Config G n→Poly Γ)
    (hz:∀x ξ U,(h x ξ U).part Γ.quiet=0)
    (sold:∀x i U,Summable (fun j=>(T.menu.terms x).tagged i j U)) (x:X) (U:Config G n) :
    ((replace T (tape T h)).leaf x).contents.cluster U=Poly.pass (total P (h x) U)*(T.leaf x).contents.cluster U ∧
    ((replace T (tape T h)).leaf x).density U=Poly.pass (total P (h x) U)*(T.leaf x).density U := by
  have eq:=QLocalCompulsoryInventoryProduct.cluster (T.menu.terms x) ((replace T (tape T h)).menu.terms x)
    (h x) (hz x) (fun i W=>each T h hz x i W (sold x i W)) U
  exact ⟨eq,cluster_density T (tape T h) x U _ eq⟩

theorem native (T:Taste X o P Γ) (h:X→Site n→ Config G n→Poly Γ)
    (hz:∀x ξ U,(h x ξ U).part Γ.quiet=0) {d κ u c b t:ℝ} {w:V→ℝ}
    (well:P.activities.Valid P.p d κ) (live:∀x,(T.menu.terms x).Active)
    (fare:∀x,(T.menu.terms x).Radial w u c b t) (x:X) (U:Config G n) :
    ((replace T (tape T h)).leaf x).contents.cluster U=Poly.pass (total P (h x) U)*(T.leaf x).contents.cluster U ∧
    ((replace T (tape T h)).leaf x).density U=Poly.pass (total P (h x) U)*(T.leaf x).density U :=
  funded T h hz (fun y i W=>((T.menu.terms y).baseBound (live y) (fare y) well W).1 i) x U

theorem row_price (T:Taste X o P Γ) (h:X→Site n→ Config G n→Poly Γ)
    (hz:∀x ξ U,(h x ξ U).part Γ.quiet=0) {w:V→ℝ} (hw:∀v,0<w v) (x:X) (i:ℕ) (U:Config G n)
    {δ:ℝ} (paid:Poly.price w (localCharge P (h x) i U)≤δ) (small:δ≤1) :
    Poly.price w (extra (T.menu.terms x) (h x) i U) ≤ 2*δ*Poly.price w ((T.menu.terms x).each i U) :=
  (Poly.multiplication hw ..).trans (mul_le_mul_of_nonneg_right
    (QLocalMarkedSpectator.relative hw _ (local_quiet _ (hz x) i U) paid small) (Poly.nonnegative hw _))

end YM.Integration.QLocalCompulsoryInventoryBank
