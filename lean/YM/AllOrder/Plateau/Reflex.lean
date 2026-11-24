import YM.AllOrder.Plateau.Minutes
/-! # mirror projection of CURVED packets preserves usable holomorphic representative across
all periods and global-stencil even on unhealthy/border crossings (unmasked identity). Masks transfer later. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open AbsoluteSums Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n m: Side} {k j w N : ℕ}
variable {σ C Z β x₀:ℝ}
local notation "E"=>Positions (Primary n G)
open Trio Slide
variable {ι:Type} (U:ι→ℝ) ( T:Repertoire ι G) (A:BillBoard U T N)
def shelter (v:ι)(b :ℝ)(W k:ℕ)(n:Side) : Offer G n:= ∑ l∈ Finset.range (k+1),∑ r:Fin (l+1), (- ratioW b l (r.val+2)) • anchorV (T l r v) W n
lemma shelter_turn (x:ι)(b:ℝ): Mirrors (shelter T x b w k n) := by intro i s p V; unfold shelter; simp_rw [Finset.sum_apply,Pi.smul_apply,show ∀ k (A:Packet G k),anchorV A w n i (pull s p V)=_ from fun k A=>anchor_turn A w n i s p V]
lemma shelter_local (x:ι)(b:ℝ): gardenfold w (shelter T x b w k) := by intro m n i j U V h; unfold shelter; simp_rw [Finset.sum_apply, Pi.smul_apply, show ∀ k (A: Packet G k), anchorV A w m i U= anchorV A w n j V from fun k A=> anchor_local A w m n i j U V h]
include A
lemma shelter_reg (hk:k≤N)(b:ℝ)(i:ι)(p: BudgetPoint)(x:Site n): p.Regular univ (shelter T i b w k n x):= by unfold shelter; simp_rw [Finset.sum_apply]; refine Meadow.regularA _ fun i hi=> Meadow.regularA _ fun j _=>AnalyticBridge.CouplingShape.reg_scale _ ?_; have he:= mem_range.mp hi; have h:= A.birth i (by omega) j; exact anchor_reg _ h.1 (h.2.2 _|>.1) (h.2.2 _|>.2) p w x
omit A
def wealth (i:ι)(b:ℝ)(W k:ℕ)(n:Side) : Config G n→ℝ:=∑ l∈ Finset.range (k+1), ∑ r:Fin (l+1), ratioW b l (r.val+2) • orbitRaw (crop W ∘ (T l r i))
lemma wealth_eq (n:Side)(i:ι)(b:ℝ)(x:Positions (Primary n G)): peal T i b w k n x= wealth T i b w k n (represent (tint G _ x)):= by simp only [peal,wealth,Finset.sum_apply]; rfl -- adduhm
lemma froth_shelter (i:ι)(b:ℝ): froth (shelter T i b w k n)= -wealth T i b w k n := by
 ext1 x; unfold froth wealth shelter; simp only [Pi.neg_apply,Finset.sum_apply,← Finset.sum_neg_distrib, Pi.smul_apply, neg_smul,smul_eq_mul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun v _=> ?_ ; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun r _=>?_ ; simp_rw [Finset.sum_neg_distrib,← Finset.mul_sum]; rw [anchor_whole]
include A in
lemma wealth_one (hk:k≤N)(b:ℝ)(i:ι)(w:ℕ): wealth T i b w k n 1=0:= by
 rw [show (1:Config G n)=represent (tint G _ (0:Positions (Primary n G))) from (by rw [map_zero]; exact Precision.link_one.symm), ← wealth_eq]; let hh:Nonempty ι:= ⟨i⟩; exact peal_zero U A hk i b -- not T H maybe Nonempty
omit U A
-- stronger than `cruising`; full fields. no book compatibility on Hart; pure E model into reclosed Footprint (orientation leaf masks hold size; deal ledger symmetry exposures later). Adapt proof around local equality and angular ε.
variable {Y:Stars→Side} (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (f:∀ c:Side,Offer G c) (h:∀ c,Mirrors (f c)) (hg: gardenfold k f) (V:Config G n)
local notation "A'"=>fun i:Stars=>f (Y i)
def stroll (i:Stars)(x:Site (Y i))(o: Site n):= Trio.unit Q A' i x (emerge Q i x o) V
include h Q
lemma priced (he:2*k≤w) (x:Site n)(i:Stars)(y:Site (Y i)):
 let p:= emerge Q i y x; let W:= Slide.shape (pad Q i) p V; stroll Q f V i y x= f (Y i) (Slide.ascended (Q i) y) W ∧ Agrees (Lattice.box k) (expandAt (Slide.ascended (Q i) y) W) (Slide.thing (Slide.charm (w+i.val) k y) x V):= by
 intro p W; refine ⟨?_, Slide.wandered (Q i) (he.trans (Nat.le_add_right ..)) y x V⟩; obtain ⟨v,hv⟩:=Slide.snap (Q i) y; rw [←hv, ← add_zero ((Slide.slant v).act y),show (Slide.slant v).act y+0= affine (Slide.slant v) 0 y from rfl, ← h]; rw [show pull (Slide.slant v) 0 W=W from Slide.traps (Q i) v V p]; rfl
include hg in
lemma same_road (hp:0<k)(he:2*k ≤ w)(x:Site n): (∑ i:Stars, ray i*∑ y:Site (Y i), stroll Q f V i y x)= f n x V:= by
 choose v hv using presents (Q 0) (Z:=k) (he.trans (Nat.le_add_right ..)) hp; let P (p: Petals k):= stroll Q f V (0:Stars) (v p) x; have hh(i:Stars)(y:Site (Y i)):= priced Q f h V he x i y; have hz(i:Stars)(y:Site (Y i)): stroll Q f V i y x=P (charm (w+i.val) k y):= by
    obtain ⟨h₁,h₂⟩:= hh i y; let p:= charm (w+i.val) k y; let z:=v p; obtain ⟨hx,hz⟩ := hh 0 z; rw [show charm (w+(0:Stars).val) k z=p from hv p] at hz; rw [h₁,show P (charm (w+i.val) k y)= _ from hx]; exact hg _ _ _ _ _ _ (fun i hi hj=>(h₂ i hi hj).trans (hz i hi hj).symm)
 simp_rw [hz,Slide.collects _ hp he Q P]; unfold P; obtain ⟨h0,hx⟩:= hh 0 (v (rosy k)); rw [h0]; rw [show charm _ _ _=Slide.rosy k from hv _,Slide.self] at hx; exact hg _ _ _ _ _ _ hx
omit h Q
lemma glid (f:∀ c:Side,Offer G c) (h:gardenfold k f): gardenfold k fun c i=> Boulevard.stillA (f c i) := by intro c d x y U V he; exact congr_arg₂ (·-·) (h _ _ _ _ _ _ he) (h _ _ _ _ 1 1 (fun _ _ _=>rfl))
include Q h hg
lemma fare_Lad (hp:0<k)(he:2*k≤w): Trio.froth (ornament Q A') V= Boulevard.stillA (Trio.froth (f n)) V:= by
 let F(c:Side)(i:Site c) := Boulevard.stillA (f c i); let U':= rip A'; have hh(z:Site n):=same_road Q F (fun i=> Trio.trimmed (h i)) (glid f hg) V hp he z; have hz: ∑ i: Site n,F n i V=Boulevard.stillA (Trio.froth (f n)) V:= by unfold F Boulevard.stillA froth; simp_rw [Finset.sum_sub_distrib]
 rw [← hz]; simp_rw [← hh]; unfold Trio.froth ornament beacon; rw [Finset.sum_comm]; conv_rhs=> rw [Finset.sum_comm]
 refine Finset.sum_congr rfl (fun i _=>?_); rw [← Finset.mul_sum,← Finset.mul_sum]; apply congr_arg; rw [Finset.sum_comm]; conv_rhs=> rw [Finset.sum_comm]
 refine Finset.sum_congr rfl fun v _=>?_ ; rw [show ∑ j: Site n,stroll Q F V i v j= _ from Equiv.sum_comp (Equiv.subRight (wrap n (Slide.stage (pad Q i) v))) (fun j:Site n=> Trio.unit Q (fun i=> F (Y i)) i v j V)]
end YM.AllOrder.Plateau
