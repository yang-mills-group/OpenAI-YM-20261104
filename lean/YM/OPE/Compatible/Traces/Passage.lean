import YM.OPE.Compatible.Ticks.Leaves
/-! Simultaneous timed pulses, retention until each pulse has passed.
Keeps Guard so that actual signed combinations can be started upon one bill.
-/
set_option linter.unusedSectionVars true
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Wilson Extra.Multi Marker Local Extra.Histories Extra.Trajectories MeasureTheory
open scoped Topology Classical
variable {G:Gauge} {C:Family G}(A:Allot C){V I J :Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
     [Fintype J][DecidableEq J](P:Ensemble V)
variable {N p k j m b:ℕ}
abbrev Lights (A:Allot C) (P:Ensemble V)(N p:ℕ) (k:I→ℕ)(j b:ℕ) (E:Track C.path V p)(o:I→Track C.path V p) := ∀ i: I, Line A P N p (k i) j b E (o i)
namespace Lights
variable {A P} {E:Track C.path V p} {o:I→Track C.path V p} {l:I→ℕ} (L:Lights A P N p l j b E o)
    (χ:Guard (Names V I))
def tips := fun i=> (L i).X j
def asks := fun i=> (L i).w j
def bottom := fun i=> (L i).w (l i)
lemma steered {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {P : Ensemble V} {N p j b : ℕ} {E : Track C.path V p} {o : I → Track C.path V p}
    {l : I → ℕ} (L : Lights A P N p l j b E o) (i:I): (L.tips i).home=o i j:= (L i).hold.steers _ (L i).hold.clock le_rfl
lemma asks_pos {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {P : Ensemble V} {N p j b : ℕ} {E : Track C.path V p} {o : I → Track C.path V p}
    {l : I → ℕ} (L : Lights A P N p l j b E o) (i:I) : 0<L.asks i:= (L i).hold.fees j (L i).hold.clock le_rfl
lemma bottom_pos {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {P : Ensemble V} {N p j b : ℕ} {E : Track C.path V p} {o : I → Track C.path V p}
    {l : I → ℕ} (L : Lights A P N p l j b E o) (i:I) : 0<L.bottom i:= (L i).hold.fees _ le_rfl (L i).hold.clock
variable (Y:Config G (C.S.side j p)→Marker.Poly (Names V I))
structure LitUp : Prop where
   live : Integrable Y (prior G _)
   owns : Owned χ (C.path.rep N p j) (E j) P L.tips L.asks ((C.path.levels.budget j).supportExponent-3) Y
-- addresses at each step
private lemma hPos {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {P : Ensemble V} {N p j b : ℕ} {E : Track C.path V p} {o : I → Track C.path V p}
    {l : I → ℕ} (L : Lights A P N p l j b E o) (i:ℕ)(k:I)(hv:l k ≤ i)(hB:i ≤ j):0 < (L k).w i:= (L k).hold.fees i hv hB
def lowers (hi:∀ i,l i ≤ m)(hm:m ≤ j) : Lights A P N p l m b E o:=fun i=> (L i).cut (hi i) hm
variable (V I) in
@[simp] def pegs (o:I→Track C.path V p)(i:ℕ)(j:V×I):= o j.2 i j.1 -- coverage
variable {Y}
lemma cover_homes (h:m ≤ j)(hp:∀ i,l i ≤ m):pegs V I o m=tags ((L.lowers hp h).tips):= funext fun i=>(congr_fun (((L.lowers hp h)).steered i.2) i.1).symm
lemma rim : pegs V I o j=tags L.tips:= funext fun i=> (congr_fun (L.steered i.2) _).symm
variable (A)
variable {A}
def Occluded (A:Allot C)(k j:ℕ)(o:I→Track C.path V p):Prop:=∀ i,k ≤ i→ i<j→ Occupancy (pegs V I o (i+1)) (A.r i) ∧ Occupancy (pegs V I o i) (A.r i)
def Margins (b k j:ℕ)(o:I→Track C.path V p):Prop:=∀ i,k ≤ i→ i< j→ χ.Border (C.path.levels.budget i).B (gapL C b i) (pegs V I o i)
lemma LitUp.descends (H:L.LitUp χ Y) (hA:C.Makes) (he:m ≤ j)(hp:∀ i,l i ≤ m) (hb:j ≤ N) (hC:C.ref 0≤ m)
    (hJ: Migrating C.path m p j E)(hχ:χ.Chordal P.v P.perms)(ht:Occluded A m j o)(hW:Margins χ b m j o):
    (L.lowers hp he).LitUp χ (gust C.path N p j Y m he):= by
    have hr(i:I) : Run P A.D N p m j E (o i) (L i).X (L i).w:= (L i).hold.crop (hp i) he le_rfl
    refine ⟨gust_live C.path _ _ _ _ H.live _,whole χ hr hχ hb hJ hA.wilson (fun i h hc=> A.admits (hC.trans h) (hc.trans_le hb)) (pegs V I o) (fun i hi hk x=>rfl) ht (fun i hi he=>?_) H.owns H.live le_rfl he⟩
    let δ:= renal C.path.levels; have ht : 0 < δ i:= (A.arcPars (hC.trans hi)).funs.1
    exact Guard.lanes χ (hW i hi he) (fun j=>mul_pos ht (hr j.2|>.fees _ (hi.trans i.le_succ) he)) (fun j=> (hr j.2).fees _ hi he.le) (fun j=> gap_hi C _ _ ((L j.2).guard' i ((hp j.2).trans hi) he) ((hr j.2).fees _ (hi.trans i.le_succ) he)) (C.path.levels.budget i).B_pos
-- extend
end Lights
end YM.OPE.Allot
