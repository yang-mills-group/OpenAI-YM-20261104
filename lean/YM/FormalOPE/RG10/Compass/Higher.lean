import YM.FormalOPE.RG10.Compass.Kettle
import YM.FormalOPE.RG10.Position.Sample
/-! # Common rotation through larger horizons. Keep distinct lifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Compass
open Function Wilson Lattice Gauge Precision Source PertExtension Filter RG PertExtension.LatticePT
  Finset RG10.Position InversionTop Orb LatticePT PowerSeries Chart
open Extra.FD Maxwell Labels Plan Deck InversionWard FlatFeed
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {d:ℕ}{n:Side}
local notation "K" => Kernel (Unit × Dir G n)
variable {F:Frames G}
variable (P:Plan F)(ε:ℝ)(s:Signed)(q u:Site n)

lemma spice (w: LatticePT.Word G) : rental w q ε=bowl (Stamp.native q w.sound w.chosen) w.chosen w.sound ε (w.F.basis w.axis):= by
 unfold rental; rw [stirring,w.F.coords_basis]; apply sum_congr rfl; intro i _; unfold LatticePT.Word.cost ordered; push_cast; rw [Pi.smul_apply,smul_eq_mul,Vertex.true_coefficients]

local notation "✣" => membrane P.H P.source P.sound P.chosen P.liftOff
local notation "†" d=> Stamp.native (G:=G) q (P.sound d) (P.chosen d)

theorem refreshing (x:Token F) : (✣) x q ε= bowl († x.1) (P.chosen x.1) (P.sound _) ε (P.liftOff.lift x.1 (owner x)):= by
 rw [← tinted P.liftOff P.certified]; simp_rw [map_sum,map_smul]; unfold membrane; apply sum_congr rfl; intro i _
 rw [spice,exteriorD]; rfl

local notation "S" d=> RG10.Position.Grade.swing (F:=F) d s
local notation "O" => pullMarks
private lemma owner_in (i:Deck F d) : higher F (price_bound F d i) (owner (token F d i))= deck F d i:=by unfold owner Deck.token; rw [cabin]; rfl
private lemma sumGrade {M:Type*} [AddCommMonoid M] [SMulWithZero ℂ M](φ:Deck F d→M)(a:Fin (d+1))(w:Spur F a.val) : ∑j:Deck F d, (((S d) ⟨a,w⟩ j):ℂ) • φ j=∑ i: Spur F a.val, (((S d) ⟨a,w⟩ ⟨a,i⟩):ℂ) • φ ⟨a,i⟩ := by
   rw [Fintype.sum_sigma]; apply sum_eq_single_of_mem a (mem_univ _); intro b _ hb; apply sum_eq_zero; intro i _; rw [RG10.Position.Grade.swing_grade d s _ _ (show a.val≠b.val from fun he=> hb (Fin.ext he.symm)), Complex.ofReal_zero,zero_smul]

lemma acrossWeight (a:Fin (d+1))(w:Spur F a.val) : ride F s.ortho a.val (owner (token F d ⟨a,w⟩)) = ∑ i: Spur F a.val, (((S d) ⟨a,w⟩ ⟨a,i⟩):ℂ) • owner (token F d ⟨a,i⟩) := by
 apply Extra.FD.writes_inj F a.val
 let hu : a.val≤d := by have he:=a.isLt; omega
 let b:=deck F d; rw [← writes_higher F hu, ← writes_higher F hu, ← ride_high]; congr 1
 let e (i:Spur F a.val) := ((S d) ⟨a,w⟩ ⟨a,i⟩:ℂ)
 dsimp only [Deck.token]; rw [map_sum]
 have he (i: Spur F a.val) : higher F hu (owner (F:=F) ⟨a.val,i⟩)= (deck F d) ⟨a,i⟩:= owner_in (F:=F) (d:=d) ⟨a,i⟩
 change _ = ∑ i:Spur F a.val, higher F hu (e i • (owner ⟨a.val,i⟩))
 simp_rw [map_smul,he]
 dsimp only [e]; rw [← sumGrade]; simp_rw [RG10.Position.Grade.swing_deck]; exact (b.sum_repr _).symm

lemma acrossSlots (i:Deck F d) : bowl (O (P.chosen i.1.val) (P.sound _) s u q) (P.chosen _) (P.sound _) ε (P.liftOff.lift _ (owner (token F d i))) = ∑ j: Deck F d, outside (C (((S d) i j):ℂ))* (✣) (token F d j) (affine s u q) ε := by
 rw [swing,P.certified.oriented]
 rcases i with ⟨a,v⟩; simp_rw [← exteriorD]; rw [acrossWeight,sumGrade]; simp_rw [map_sum]
 apply sum_congr rfl; intro i _; dsimp only [Deck.token]; erw [map_smul, map_smul]; exact congr_arg _ (refreshing P ε _ (F:=F) (n:=n) ⟨a.val,i⟩).symm

variable {u} (hu:-u=u) (hn: Even n.val) {I:Type*}[Fintype I]
local notation "t" => feed (G:=G) hn
local notation "E" => vertices G n
local notation "e" => epsilon

include hu

theorem locality (x:I→Site n) (v:I→Deck F d) :
 (t).ordinary E univ (fun i=> (✣) (token F d (v i)) (x i) ε)= ∑ A:I→Deck F d,
    (∏ i,C (((S d) (v i) (A i)):ℂ)) * (t).ordinary E univ (fun i=> (✣) (token F d (A i)) (affine s u (x i)) ε):= by
 let b (i:I) := token F d (v i)
 let K' (i:I) := (F.level (b i).1).Index
 let z i:= P.liftOff.lift (b i).1 (owner (b i)); let p i:= P.chosen (b i).1; let h i:= P.sound (b i).1
 let g (i) : K' i→ Series:= fun k=> PowerSeries.C (ordered (p i) (h i) ε ((F.level (b i).1).coords (z i)) k)
 let A i:= Stamp.native (x i) (h i) (p i); let B i:= pullMarks (p i) (h i) s u (x i)
 let U i:= (bowl (B i) (p i) (h i) ε) (z i); let V i:= (bowl (A i) (p i) (h i) ε) (z i)
 have ht (A:∀i:I,K' i→Stamp G n) : (t).ordinary E univ (fun i=> bowl (A i) (p i) (h i) ε (z i)) =∑ j:∀i,K' i, (∏ i,g i (j i))* (t).ordinary E univ (fun i=>(A i (j i)).couplingMark) := by
   simp_rw [stirring]; exact (combination g (fun i j=>(A i j).couplingMark) (fun j : ∀i,K' i=> Stamp.integrals hn (fun i=>A i (j i)) univ)).2
 have hy : (t).ordinary E univ U = (t).ordinary E univ V:= by
   unfold U V; rw [ht,ht]; apply sum_congr rfl; intro i _; apply congr_arg (fun x:Series=>_*x); exact Rotation.transports hn s hu (A:=fun k=>A k (i k)) (B:=fun k=> B k (i k)) univ (fun _ _=> rfl) (fun _ _=> rfl)
 calc
  _ = (t).ordinary E univ V:= by simp_rw [refreshing]; rfl
  _ = _ := hy.symm
  _ = _ := by
    unfold U B h p z b
    change (feed hn).ordinary _ univ (fun i=> bowl (pullMarks (P.chosen (v i).1.val) (P.sound _) s u (x i)) (P.chosen _) (P.sound _) ε (P.liftOff.lift _ (owner (token F d (v i)))))=_
    simp_rw [acrossSlots]
    exact (combination (J:=fun _=>Deck F d) (fun (i:I) j=> C (((S d) (v i) j):ℂ)) (fun i j=> (✣) (token F d j) (affine s u (x i)) ε) (fun j=> (curtain hn _ _ _ _ _ _ _ _).1)).2
end YM.FormalOPE.RG10.Compass
