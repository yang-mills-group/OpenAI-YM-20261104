import YM.GradedFar.Physical.Scholars
import YM.OPE.Orbits.Continuity

/-!
# Keep whole receipts at the pair-integrals, including at the true packet
-/
namespace YM.FVA2.GradedFar.Physical.Tasks
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged Physical.Round
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (K : FramesH P)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
lemma booked_margins {X:Set (Points n)}(hX:IsCompact X)(hx:X⊆conf n)(m:ℕ) : ∀ᶠ r in τ,∀ x∈X,∀ o:E4,∀ j≤ m,
    orbitMargin Q.port j (atPos r o x) o := by
    obtain ⟨T,c,hT,hc,h⟩:=smooth_hill hX hx
    filter_upwards [admissible_separated (I:=Fin n) U Q hT.le hc m,self_mem_nhdsWithin] with r hr (hp:0<r) x hx o
    exact hr (atPos r o x) o
       ⟨fun i=> by rw [atPos,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hp.le,mul_comm]; gcongr; exact (h x hx).1 i,
        fun i j he=>by simp only [atPos, add_sub_add_left_eq_sub, ← smul_sub,norm_smul, Real.norm_of_nonneg hp.le]; rw [mul_comm c]; exact mul_le_mul_of_nonneg_left ((h x hx).2 _ _ he) hp.le⟩

lemma entitled {X:Set (Points n)}(hX:IsCompact X)(hx:X⊆conf n){Y:Set (Points m)}(hY:IsCompact Y)(hy:Y⊆Outside m)
    (Q:Set Continuation.Window) : ∀ᶠ (w:Continuation.Window) in windows Q, ∀ x∈X,∀y∈Y,∀o:E4,
       Injective (beside (atPos w.len o x) (atPos w.Coarse o y)) := by
   obtain ⟨M,δ,hM,hδ,hA⟩:=terrain hX hx hY hy
   filter_upwards [(windows_separation _).eventually hA, (windows_short _).eventually self_mem_nhdsWithin] with w h (hr:0<Window.len w) x hx y hy o; exact Fork.unique_part (x:=x.ofLp) (y:=y.ofLp) (M:=M) (show Fork.Landed _ _ _ _ _ _ from (by obtain hh:=h (Window.len w) hr _ hx _ hy; exact ⟨hh.pos,hh.younger,hh.xcap,hh.ycap,hh.ynear,hh.xsep,hh.ysep,hh.together⟩)) o hδ
-- Term projection
structure Data (X:Set (Points n))(Y:Set (Points m))(I:Type)[TopologicalSpace I] where
    o: I→E4
    x: I→ Points n
    y: I→ Points m
    viewer: Viewers U
    lived: ∀ i, x i∈X
    tall: ∀ i, y i∈Y
    ox: Continuous o
    ax: Continuous x
    ay: Continuous y
variable {X:Set (Points n)}{Y:Set (Points m)} [TopologicalSpace I]
    (v:Viewers U)(o:I→E4)(ho:Continuous o)(x:I→Points n)(hx:Continuous x)(y:I→Points m)(hy:Continuous y)
    (t:ℝ)(w:Continuation.Window)(u:Inputs G d)(s:Inputs G e)
local notation "V"=>fun i=>(v,o i)
include ho hx hy
omit hy in
lemma pose_continuous (q:ℝ): Continuous (fun i=> atPos q (o i) (x i)) := by unfold atPos; fun_prop
lemma stager (hx':∀ i,Injective (beside (atPos w.len (o i) (x i)) (atPos w.Coarse (o i) (y i)))) :
     Continuous (fun i=> Ywide U K w (V i) (x i) (y i) u s) :=by
    let ψ i:Loc (Fin n) (Fin m):=(atPos w.len (o i) (x i),o i,atPos w.Coarse (o i) (y i)); have hp:Continuous ψ:=(pose_continuous o ho x hx _).prodMk (ho.prodMk (pose_continuous o ho y hy _))
    exact continuous_iff_continuousAt.mpr fun i=> (Orbits.whole_cont_at (C:=R) (x:=ψ i) (here K w.len u) (here K w.Coarse s) (spectator U v) (spectate U v) (hx' i)).comp hp.continuousAt

omit hy in
lemma packet_cont (hx':∀ i: I,∀ j≤h,orbitMargin Q.port j (atPos t (o i) (x i)) (o i)) :
    Continuous (fun i=> chair G h (packet U K Q d h t (V i) (x i) u)) := by
    let ψ i:=(atPos t (o i) (x i),o i); have hp:Continuous ψ:= (pose_continuous o ho x hx t).prodMk ho
    let A (j:Fin (h+1)) i:= Q.fresh j.val (atPos t (o i) (x i)) (o i) (here K t u)
    have ha (j:Fin (h+1)):Continuous (A j):= continuous_iff_continuousAt.mpr fun i=>
      (Q.fresh_smooth _ _ _ (v:=here K t u) (hx' i j.val (by omega))).continuousAt.comp (f:=ψ) hp.continuousAt
    exact (mapK K t h).symm.continuous.comp (continuous_finsetSum Finset.univ fun (j:Fin (h+1)) _=>
      ((U.sector.derivatives.rise (d:=j.val) (e:=h) (Nat.le_of_lt_succ j.isLt)).continuous_of_finiteDimensional.comp (ha j)))

omit hx in
lemma central (a:I→ Sec G h)(hA:∀ j:Toon G h, Continuous (fun i=> coord j (a i)))
   (hx:∀ i, Injective (beside (atPos w.len (o i) (0:Points 1)) (atPos w.Coarse (o i) (y i)))) : Continuous (fun i=>Dwide U K w (V i) (y i) s (a i)) := by
    have he i:Dwide U K w (V i) (y i) s (a i)=∑ j:Toon G h,coord j (a i)*Dwide U K w (V i) (y i) s (theory j):= by
       simp_rw [← receive_leg]; conv_lhs=> arg 2; rw [← reconstructed (a i)];
       simp_rw [map_sum,_root_.map_smul]; rfl
    simp_rw [he]; exact continuous_finsetSum _ fun j _=>(hA j).mul (stager U K v o ho (fun _=> (0:Points 1)) continuous_const y hy w (d:=fun _=>h) (fun _=>theory j) s hx)
end
end YM.FVA2.GradedFar.Physical.Tasks
