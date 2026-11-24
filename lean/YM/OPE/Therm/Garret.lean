import YM.OPE.Therm.Lockets
import YM.Branch.Predict
/-!
# Free links in a site-seam cell. Single seam configuration, all rooms

Finite graph reflection (no field continuations). Folds use oriented edges;
need n sufficiently large just to read an edge unambiguously from head-chain.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.House
open Function Filter RG Lattice Wilson MeasureTheory Cells
open scoped BigOperators Classical Topology
variable {n:Side} {G:Gauge}
variable (T:Tiling n)(hv:T.kind=.site) {v u:T.Cell} {x y:Site n} {a i:Axis} {r:ℕ}
local notation "γ"=> T.coordinated
local notation "N"=>T.side.val
local notation "φ"=>T.residue
local notation "∆"=> T.chamber
local notation "𝒞"=> Config G n
local notation "E" => Edge (Site n)
local notation "c"=>T.copyMap
local notation "σ"=>T.omega
local notation "b"=>T.translateBy

def topE (e:E): Site n:=e.1+step e.2
def links (X:Set (Site n)): Finset E:= Finset.univ.filter (fun e=>e.1∈X ∧ topE e∈X)
def stays (X:Set (Site n)) : Finset E:=Finset.univ.filter (fun e=>e.1∈X ∨ topE e∈X)
def fullRoom (v:T.Cell): Finset (Edge (Site n)) := links (n:=n) (suite T v)
-- AND full, no outer spill; simpler than prove no edge escaping
-- from chamber. This suffices for paying conditional interiors, which stay within.
def edges (v:T.Cell):=fullRoom T v ∩ stays (T.chamber v)
def seam : Finset E:= Finset.univ \ Finset.univ.biUnion (edges T)
variable {e:Edge (Site n)}
lemma linn {X:Set (Site n)}: e∈ links X ↔ e.1∈ X ∧ topE e∈ X := by simp [links]
lemma touches {X:Set (Site n)}: e∈ stays X ↔ e.1∈ X ∨ topE e∈ X := by simp [stays]
lemma lin_room : e∈ fullRoom T v ↔ hall T v e.1 ∧ hall T v (topE e):=by unfold fullRoom; rw [linn]; simp only [Finset.mem_coe,host]
lemma mem_free : e∈edges T v ↔ e∈ fullRoom T v ∧ (e.1∈∆ v ∨ topE e∈∆ v):=by rw [edges,Finset.mem_inter,touches]
lemma holds : edges T v ⊆ fullRoom T v:= Finset.inter_subset_left
lemma books : links (∆ v) ⊆ edges T v:= by
   intro e he; obtain ⟨hp,hP⟩:= linn.mp he; exact (mem_free T).mpr ⟨(lin_room T).mpr ⟨enters T hp, enters T hP⟩, Or.inl hp⟩
lemma wraps : e∈ seam T ↔ ∀ v,e∉ edges T v:=by simp [seam]
lemma sealing (v:T.Cell) : Disjoint (seam T) (edges T v):=Finset.disjoint_left.mpr (fun _ he=> (wraps T).mp he _)
include hv in
lemma splits (he:e ∈ fullRoom T v)(hf:e∈ edges T u): v=u:=by
  obtain ⟨hp,hP⟩:= (lin_room T).mp he; refine Eq.symm ?_; rcases ((mem_free T).mp hf).2 with ht|ht; exact entrance T hv ht hp; exact entrance T hv ht hP
include hv in
lemma sails (v:T.Cell) : fullRoom T v ⊆ seam T ∪ edges T v:=by
  intro e he; by_cases h:e∈edges T v; · exact Finset.mem_union_right _ h
  exact Finset.mem_union_left _ ((wraps T).mpr fun i hi=> h ((splits T hv he hi).symm ▸ hi))
include hv in
lemma aside : Pairwise (fun i j=>Disjoint (edges T i) (edges T j)):=fun i j h=> Finset.disjoint_left.mpr (fun _ hx hy=> h (splits T hv (holds T hx) hy))

section turn
def twist (s:Signed)(y:Site n): Equiv.Perm E:= Equiv.ofBijective (sendEdge s y) ⟨sendEdge_injective s y,Finite.injective_iff_surjective.mp (sendEdge_injective s y)⟩
lemma sweet {s:Signed}{z:Site n} (h:s.flip e.2=false) : twist s z e=(affine s z e.1,s.perm e.2) ∧ topE (twist s z e)=affine s z (topE e):=by
   have he:sendEdge s z e=(affine s z e.1,s.perm e.2):= by simp [sendEdge,Step.rotate,posDir,Step.used,h]
   change _=_ ∧ topE (sendEdge s z e)=_; refine ⟨he,?_⟩; rw [he]; exact (StepData.possite s z e.1 e.2 h).symm
lemma sour {s:Signed}{z:Site n} (h:s.flip e.2=true): twist s z e=(affine s z (topE e),s.perm e.2) ∧ topE (twist s z e)=affine s z e.1:=by
   have hf:=StepData.negsite s z e.1 e.2 h
   have he:sendEdge s z e=(affine s z e.1-step (s.perm e.2),s.perm e.2):=by simp [sendEdge,Step.rotate,posDir,Step.used,h]
   change sendEdge s z e=_ ∧ topE (sendEdge s z e)=_; rw [he, show topE e=e.1+step e.2 from rfl,hf]; exact ⟨rfl,(by unfold topE; simp only [sub_add_cancel])⟩
lemma turnAny (s:Signed)(z:Site n){X Y:Set (Site n)}(h:∀ x:Site n, x∈ X ↔ affine s z x ∈ Y) (e:E) :
    (e∈ links X ↔ twist s z e∈ links Y)∧ (e∈stays X ↔ twist s z e∈ stays Y) := by
   simp only [linn,touches]; cases he: s.flip e.2
   · rw [(sweet (z:=z) he).2,(sweet (z:=z) he).1]; simp only [h,true_and]
   rw [(sour (z:=z) he).2,(sour (z:=z) he).1]; simp only [h]; tauto
include hv
lemma marches (i:T.Cell): e∈ fullRoom T 0 ↔ twist (σ i) (b i) e∈ fullRoom T i:=
   (turnAny (σ i) (b i) (X:=suite T 0) (Y:=suite T i) (fun x=>by simpa only [Finset.mem_coe,host] using! (turnsHall T hv i x).symm) e).1
lemma ticket (i:T.Cell): e∈ edges T 0 ↔ twist (σ i) (b i) e∈ edges T i:= by
   unfold edges;rw [Finset.mem_inter,Finset.mem_inter,marches T hv i, (turnAny (σ i) (b i) (X:=∆ 0) (Y:=∆ i) (T.reflected_chamber · i) e).2]
end turn
section fold
variable {hn:2≤T.side.val}
-- V any global config; give pointwise all-folded. No H on V except matching later.
def zig (x:Site n) : Site n:= fun a=> T.base a+ if (σ (T.which x)).flip a then (N:Per n)-φ x a else φ x a
def fromZig (V:𝒞) :𝒞:= fun e=> if zig T (topE e) = zig T e.1+step e.2 then V (zig T e.1, e.2) else (V (zig T (topE e),e.2))⁻¹
private lemma cardH (h: γ v x a ≤ N) : zig T x a=T.base a+ if (σ v).flip a then (N:Per n)-γ v x a else γ v x a:=by
   unfold zig; apply congr_arg (T.base a+·)
   rcases lt_or_eq_of_le h with h|h
   · obtain ⟨hp,ht⟩:=floorGen T h; simp only [Tiling.omega,hp,ht]; rfl
   obtain ⟨-,hp,hP⟩:=hiCoord T h; simp only [Tiling.omega,h,hp,hP,T.parity_add,T.parity_one,decide_eq_true_eq,ne_eq,Nat.cast_zero]; have ht (f:ZMod 2): f=0 ∨ f=1:=by fin_cases f <;> simp [ZMod]
   rcases ht (T.parity (v a)) with ha|ha <;> simp [ha,show (1:ZMod 2)+1=0 from rfl]
include hv
lemma grabs (v:T.Cell) (h:hall T 0 x): zig T (c v x)=x:=by
   ext1 a; rw [cardH T ((turnsHall T hv v x).mpr h a), cipher T hv v x a (h a)]; have he:=T.indent 0 x a; rw [T.starts_zero] at he
   cases e: (σ v).flip a; simpa only [Bool.false_eq_true,↓reduceIte]; simp only [↓reduceIte, Nat.cast_sub (h a),sub_sub_cancel]; exact he -- first target uses he
include hn
private lemma zig_hi : 2 < n.val := hn.trans_lt T.narrow
lemma hugs (v:T.Cell) (he:e∈fullRoom T 0) (V:𝒞): pull (σ v) (b v) (fromZig T V) e= V e:=by
   let s:= σ v; let T':= twist s (b v) e; obtain ⟨hp,hP⟩:= (lin_room T).mp he
   rw [WardBin.Wheels.pull_by]; change (if s.flip e.2 then (fromZig T V T')⁻¹ else fromZig T V T')=_
   have hs : s.perm e.2=e.2:=rfl
   have ha: zig T (affine s (b v) e.1)= e.1:= grabs T hv v hp
   have hb: zig T (affine s (b v) (topE e)) = topE e:= grabs T hv v hP
   cases e':s.flip e.2
   · have hc:T'=(affine s (b v) e.1,s.perm e.2):=(sweet e').1; simp only [Bool.false_eq_true,↓reduceIte]; unfold fromZig; rw [(sweet (z:=b v) e').2, hb,hc]; simp [hs,ha,topE] -- topE hb issue
   have hc:T'=(affine s (b v) (topE e),s.perm e.2):=(sour e').1; have hu : ¬ e.1=topE e + step e.2:=by
       have hh : ((step e.2+step e.2:Site n) e.2)=(2:Per n):=by simp; ring
       have hf : (2:Per n) ≠ 0:= by
           intro h; have ha := congr_arg ZMod.val h; rw [ZMod.val_zero,show (2:Per n) = ↑(2:ℕ) from rfl, ZMod.val_natCast_of_lt (zig_hi T hv (hn:=hn))] at ha; omega
       intro h; apply hf; rw [← hh]; have hp : (step e.2+step e.2:Site n)=0:= add_eq_left.mp (by rw [← add_assoc]; exact h.symm); rw [hp]; rfl
   unfold fromZig; rw [(show topE T'= _ from (sour e').2),ha,hc]; simp only [hb,hs]; rw [if_neg hu]; simp
lemma presents (v:T.Cell)(V:𝒞): Agrees (suite T 0) (pull (σ v) (b v) (fromZig T V)) V:=fun e h₁ h₂=> hugs T hv (hn:=hn) v (linn.mpr ⟨h₁,h₂⟩) V
end fold
end YM.OPE.Therm.House
