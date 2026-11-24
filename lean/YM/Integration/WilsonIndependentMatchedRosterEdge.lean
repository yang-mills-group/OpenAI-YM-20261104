import YM.Integration.WilsonIndependentMatchedCoverJoined
import YM.Integration.WilsonIndependentMatchedVacant
import YM.WilsonCoeffUV.Product.Connected.FirstJoin

/-! Simultaneous first connection on the one normalized conditional, at
arbitrary finite arity. The same complete covered inputs and all their
ordinary products occur on both sides of the deposited difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterEdge
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{D k n e u b i N:ℕ}{E W:Credit}

theorem current (R:Realm G (e+1) E)(sale:SpringD R k u b W)(live:R.anchor ≤ i)(edge:i<N)
    (l:Fin (n+1)→ℕ)(room:∑a,l a ≤ k)(φ:Fin (n+1)→Rarity D)(T:Fin (n+1)→Era G ℝ)
    (x y t z:ℝ)(o:CellR)(mesh:0<x)(fits:x*(ll R.draws i).L.val ≤ 1)(pos:0<t)
    (separate:∀a c,a≠c→ClearDay (φ a) (φ c) t)
    (radius:∀a,radiusH (φ a) (x*(ll R.draws i).L.val) y ≤ z)
    (held:∀a,(VisitsT (φ a) x y o).Nonempty)(A:Fin (n+1)→ℝ)
    (fine:∀a,Income (T a) (l a) e (u+b) (OrbP (ll R.draws i) (φ a) x y o) (A a))
    (later:∀a,Flush e u (x*(ll R.draws i).L.val) (verseI R.draws R.paid i N (l a) (T a)) (A a)):
    let η:=x*(ll R.draws i).L.val
    let earn:=(n:ℝ)*R.cash (priceWG G e k u b E W) i*pearlB u b (4*z) (t/η)*nuP (coinMat k e+1) n A
    let joined:=DeltaGap R.draws R.paid i N T l
    Auth (∑a,l a) joined ∧ Flush e u η joined earn:=by
  intro η earn joined
  let δ:=max 0 (δWarm R i (i+1))
  let profile:=fun a=>saddleP (ll R.draws i).L (VisitsT (φ a) x y o)
  have pair (a c:Fin (n+1))(hac:a≠c):SplitHill (profile a) (profile c) η (4*z) (t/η):=
    disjointly _ _ _ x y t z o mesh fits (separate a c hac) pos (radius a) (radius c) (held a) (held c)
  have paid (a:Fin (n+1)):Fringed (l a) e u η (A a) δ
      (verseI R.draws R.paid i N (l a) (T a)) (verseI R.draws R.paid i N (l a) (T a)):=
    Fringed.same (later a) (Auth.verse R.draws edge R.hG R.green (fine a).1) (le_max_left _ _)
  have bound:=drifted n T T l A profile (by linarith [(fieldCap (φ 0) _ y).trans (radius 0)] : 1≤4*z)
    (div_pos pos (mul_pos mesh (by exact_mod_cast (ll R.draws i).L.pos))) room
    (mul_nonneg mesh.le (by positivity)) pair sale live (Nat.lt_succ_self i) edge edge
    (le_max_right 0 _) (fun a=>(fine a).1) (fun a=>(fine a).1) (fun a=>(fine a).2 δ (le_max_left _ _)) paid
  exact ⟨bound.pen,bound.f_l⟩

theorem missing (T:Fin (n+1)→Era G ℝ)(a:Fin (n+1))(zero:T a=0):MassP G ℝ n T=0:=by
  induction n with
  | zero=>
    have h:a=0:=Fin.ext (by omega)
    simpa only [MassP,h] using zero
  | succ n ih=>
    rw [MassP]
    refine Fin.cases ?_ (fun j=>?_) a zero
    · intro head;rw [head];exact Prod.ext (funext fun _=>(woadNull _).2) (woadNull _).2
    · intro tail;rw [ih (Fin.tail T) j tail]
      exact Prod.ext (funext fun _=>(woadNull _).1) (woadNull _).1

theorem absent (R:Realm G (e+1) E)(edge:i<N)(T:Fin (n+1)→Era G ℝ)(l:Fin (n+1)→ℕ)
    (a:Fin (n+1))(none:T a=0):DeltaGap R.draws R.paid i N T l=0:=by
  have gone:verseI R.draws R.paid i N (l a) (T a)=0:=by rw [none,verseZero R.draws edge R.hG R.green]
  unfold DeltaGap startK
  rw [missing T a none,verseZero R.draws edge R.hG R.green,missing _ a gone,sub_self]

end YM.Integration.WilsonIndependentMatchedRosterEdge
