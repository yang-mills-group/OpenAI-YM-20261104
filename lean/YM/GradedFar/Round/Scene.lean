import YM.GradedFar.Physical.Fare
import YM.GradedFar.Physical.Away

/-!
# Physical single-arena view on the whole argument (T still fixed!)
  Use only with every input in H_r at this cap. Preserve slots,
  true center translations, real & spectral fields. On both sides use
  `(r • x), (s • y)` as they are requested, then express as `r • x,y*T`.
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus O.Score
open O O.Enh
open Moving Growth Pose Books
open Scale Dframe
open OPE Orbits Logged OPE.Logged.Deck Horizon
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t : ℕ} {I:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (J K : FramesH P)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "Φ"=>spectator U

def painted (s:Viewers U) (d : Fin n→ℕ)(r:ℝ)(x:Points n) :
    MultilinearMap ℂ (fun i=> Sec G (d i)) ℂ :=
  (P.classMoment (Φ s) d (r • x)).compLinearMap (fun i=> (K r (d i)).toLinearMap)
lemma unselected : painted U K none (fun _:Fin n=>h) = (fun r=> familyPoint U K h r n):=rfl

lemma tags_pay (q:Viewers U) (r:ℝ) (x:Points n) (v : Inputs G d) :
    painted U K q d r x v=P.useAt (Φ q) (r • x) (Orbits.tags (here K r v)):= rfl

lemma present {r:ℝ} (h:0<r){x:Points n}(hp:x∈conf n) : r • x∈ conf n:= by
    intro i j hj; exact hp (smul_right_injective _ h.ne' hj)

lemma painted_cost (q:Viewers U)(o:E4) (r:ℝ)(x:Points n)(v:Inputs G d) (hc: r • x ∈ conf n) :
    painted U K q d r x v= Orbits.moment (Φ q) (atPos r o x) (here K r v) := by
    have hx (s:E4): atPos r s x=(fun i=> (r • x) i + s):= funext fun i=>add_comm ..
    rw [hx,Orbits.carrying (S:=P) (spectate U q) hc o, Orbits.observed,named_fin (Φ q) (spectate U q).laws.toSymmetric _ hc]; rfl

include U
lemma painted_rise (q:Viewers U){r:ℝ}{x:Points n}{d':Fin n→ℕ}(v:Inputs G d)(hc:r • x ∈ conf n)(h:d ≤ d')
    (hi:∀ i,K r (d' i) (up (h i) (v i))=U.sector.derivatives.rise (h i) (K r (d i) (v i))) :
    painted U K q d r x v= painted U K q d' r x (fun i=> up (h i) (v i)):= by
    rw [painted_cost U K q 0 r x v hc, painted_cost U K q 0 r x _ hc]
    have hh: Injective (atPos r 0 x):= by
      rw [show atPos r 0 x= (r • x).ofLp by funext i; exact zero_add _]; exact hc
    rw [show here K r (d:=d') (fun i=> up (h i) (v i))= _ from funext hi]; symm; exact Logged.Subtable.moments _ _ _ _ hh

lemma scale_story (q:Viewers U)(r:ℝ)(o:E4) (x:Points n)(y:Points m)(u:Tags G h n)(v:Tags G h m)
    (hx:r • forest x y∈conf (n+m)) :
    painted U K q (fun _:Fin (n+m)=>h) r (forest x y) (Fin.append u v) =
     Orbits.whole (Φ q) (atPos r o x) (here K r (d:=fun _=>h) u) (atPos r o y) (here K r (d:=fun _=>h) v) := by
   let x':=atPos r o (forest x y)
   rw [painted_cost U K q o r (forest x y) (Fin.append u v) hx]; unfold whole; rw [Orbits.observed, Orbits.observed]
   let T:Fin n⊕ Fin m≃ Fin (n+m):= finSumFinEquiv
   let u':= Orbits.names (here K r (d:=fun _=>h) (Fin.append u v)); change observe (Φ q) x' u'= _
   have hy':Injective x':= by intro i j hj; exact hx (show (r • forest x y) i=(r • forest x y) j from add_left_cancel hj)
   rw [← perm_observe (Φ q) (spectate U q).laws.toSymmetric T u' hy']
   refine congrArg₂ (observe (Φ q)) (funext (fun i=> ?_)) (funext (fun i=>?_))
   · rcases i with i|i <;> simp [T,x',atPos,forest,points]
   rcases i with i | i <;> simp [T,u',Orbits.stages,here,Orbits.names] <;> rfl

lemma record (v:View U)(w : Window)(x:Points n)(y:Points m)(u:Tags G h n)(p:Tags G h m)
    (hp:w.len • forest x (w.Stretch • y)∈conf (n+m)) :
    Y0 U K (fun _=>h) (fun _=>h) w v x y u p= painted U K v.1 (fun _:Fin (n+m)=>h) w.len (forest x (w.Stretch • y)) (Fin.append u p) := by
    rw [Y0_value,scale_story U K v.1 w.len v.2 x (w.Stretch • y) u p hp]
    congr 1; funext i; unfold atPos Window.Coarse; rw [mul_smul]; rfl
omit U in
lemma wide_here (w:Window) (x:Points n): squeeze (-w.sep) x=w.Stretch • x:= by unfold squeeze sep; simp [Window.Stretch]

end
end YM.FVA2.GradedFar.Physical.Round
