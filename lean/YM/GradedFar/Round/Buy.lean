import YM.GradedFar.Round.Segment
/-!
# Re-read & pay at the two-zone measurements -- comparing in `Point` before split caps
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
    (E : (d:ℕ)→ℝ→FieldEnd G d) (Y : (d:ℕ)→ℝ→ Prediction G d) (θ:ℝ→ℝ)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (W : Bookshelf N U J K E Y θ) (D : Earned N M U J K θ) (hD:oriented U K)
    (ht: LogTrace U Q.port) (he:∀ᶠ r in τ, ∀ u : Sec G h,K r h u=J r h (E h r u))
    (hGrid : Grid N U J)
variable {C B:ℝ}(hC:0<C)(hB:0<B)
local notation "Q₀"=> upper G C B
local notation "Γ"=>windows Q₀
local notation "g₀"=>gYM G ∘ Window.len
variable (T:Filter I)(w:I→ Continuation.Window)(hw:Tendsto w T (windows (upper G C B)))
variable {X:Set (Points n)}{Y':Set (Points m)}(hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y')(hy:Y'⊆Outside m)
    (o:I→View U) (a:Tags G h (n+m))(S:I→ XSet X Y')
local notation "b₀"=> Duly Q₀ T w hw simple
local notation "F"=> familyPoint U K h
local notation "r"=>Window.len∘w
include simple hw
omit simple hw in
lemma ball_knob {X:Set (Points n)}{ε:ℝ} (h:0<ε)(x:Points n)(y:Points n)(hc:Metric.closedBall x ε⊆ X)(hp:dist y x≤ε):segment ℝ x y ⊆ X := ((convex_closedBall x _).segment_subset (by simpa using h.le) hp).trans hc
-- segment both blocks & envelope with *same* test; choose lumps in X' if early not admitted.
lemma pick_knob {Z:Set (Points n)}{V:Set (Points m)} {L H:ℝ} (hL:0<L)(hh:0<H) (hz : ∀ x∈X, Metric.closedBall x L ⊆ Z)
    (he':∀ y∈Y',Metric.closedBall y H⊆V){k:ℕ} (hk:0<k)(Y:Continuation.Window→XSet X Y'→Points n)(P:Continuation.Window→XSet X Y'→Points m)
    (hN : May G Q₀ _ (fun i:XSet X Y'=>i.1.val) (fun i=>i.2.val) Y P k) :
    ∃ (S0 S1:I→ XSet Z V), (∀ i, (S i).1.val=(S0 i).1.val ∧ (S i).2.val=(S0 i).2.val ) ∧
      (∀ᶠ i in T, Y (w i) (S i)=(S1 i).1.val ∧ P (w i) (S i)=(S1 i).2.val ) ∧
      ΓPath T w S0 S1 ∧ Buys T (fun i=> contour w S1 i -contour w S0 i) (g₀∘ w) k := by
    have hR i:= hz _ (S i).1.property; have hT i:= he' _ (S i).2.property
    let S0(i:I) : XSet Z V:=( ⟨_,hR i (Metric.mem_closedBall_self hL.le)⟩,⟨_,hT i (Metric.mem_closedBall_self hh.le)⟩ )
    let x i:=Y (w i) (S i); let y i:=P (w i) (S i)
    let S1(i:I): XSet Z V := if h:x i∈Z∧y i∈V then (⟨_,h.1⟩,⟨_,h.2⟩) else S0 i
    have hp: ∀ᶠ i in T, dist (x i) (S i).1.val ≤ L ∧ dist (y i) (S i).2.val ≤ H := (hw.eventually (nearby (simple:=simple) hL hh hk hN)).mono fun i h=> h (S i)
    have hS : ∀ᶠ i in T, x i=(S1 i).1.val ∧ y i=(S1 i).2.val:= hp.mono (fun i h=>by dsimp only [S1]; rw [dif_pos (show x i∈ Z ∧ y i∈V from ⟨hR i h.1,hT i h.2⟩)]; exact ⟨rfl,rfl⟩ )
    refine ⟨S0,S1,fun i=> ⟨rfl,rfl⟩,hS,?_,?_⟩
    · filter_upwards [hS,hp] with i h hp; rw [← h.1,← h.2]; exact path_location _ _ _ _ _ _ _ (ball_knob hL _ _ (hR i) hp.1) (ball_knob hh _ _ (hT i) hp.2)
    have hy:Buys T (fun i=>along (w i) (x i) (y i)-contour w S0 i) (g₀∘w) k:=
      IsBigO.comp_tendsto (rounding_distance (simple:=simple) hN) (show Tendsto (fun i=>(w i,S i)) T (comap Prod.fst Γ) from tendsto_comap_iff.mpr hw)
    exact hy.congr' (hS.mono fun i h=> by dsimp only [contour]; rw [h.1,h.2]) (EventuallyEq.refl ..)

omit simple hw in
lemma priced_fields (v : Tags G h n): ∃ T':ℝ,∀ i,Ball T' (v i) := by
   let p (i:Fin n × Toon G h):= ‖coord i.2 (v i.1)‖
   obtain ⟨C,h⟩:= Finite.bddAbove_range p
   exact ⟨C,fun i j=> h (Set.mem_range_self (i,j))⟩
include H W D ht he hD hGrid hX hx hY hy hB hC hw o
-- at least through order 1, below reduce later
set_option maxHeartbeats 400000 in
lemma receipt_lane (h6:6≤h) (p:ℕ)(hp:1≤p) : Priced b₀ p (θ∘r) 0 (fun i=> painted U K (o i).1 (fun _:Fin (n+m)=>h) (r i) (contour w S i) a)
   (fun i=>boundary N a (contour w S i)) := by
   obtain ⟨Z,hZ,h1,hz,ε,hε,HZ⟩:=enlarge_knob hX (conf_open n) hx
   obtain ⟨V,hV,h2,hv,δ,hδ,HV⟩:=enlarge_knob hY (O.Read.Outside_open m) hy
   obtain ⟨c,hc⟩:=priced_fields a
   obtain ⟨k,h0,C',hC',hq⟩:= ((eventually_gt_atTop 0).and (expected N M H U Q J K θ D hD ht hZ h1 hV h2 c h)).exists
   obtain ⟨A,hA⟩:= exists_nat_gt (((p+1:ℕ):ℝ)+k); have ha:p+1 ≤ A:= by exact_mod_cast ((by linarith : ((p+1:ℕ):ℝ)≤(A:ℝ)))
   have hA' : 0<A:=lt_of_lt_of_le (by omega) ha
   obtain ⟨Z',V',H0,H'⟩:=booked_grid (I:=I) (B:=B) N M H U J K E Y θ W D he hGrid hB hC hX hx hY hy h6 A p hp
   obtain ⟨S0,S1,hk0,hk1,hy',hLength⟩:= pick_knob (simple:=simple) T w hw S hε hδ HZ HV hA' Z' V' H0
   have hh := H' T w hw S Z V hZ h1 hV h2 S1 hk1 a
   have he' : ∀ᶠ w:Continuation.Window in Γ, ∀ x∈Z,∀y∈V,∀o:View U, LaneCosts U K a o w.len w.Coarse x y C' k :=
      (hq B C hB hC).mono (fun i h x hx y hy o=> (h _ hx _ hy).2 o a hc)
   have hz' i:contour w S i=contour w S0 i:= congrArg₂ (along (w i)) (hk0 i).1 (hk0 i).2
   have hH:= continuous_lane (simple:=simple) U K hC T w hw hZ h1 hV h2 a S0 S1 hy' C' k hC' he' hA.le hLength
   have hY':= eval_lane N M H θ D.clock T w hw hZ h1 hV h2 a S0 S1 hy'
      (budget_growth T hLength (p+1) ha (jet_level T (((shrink simple).comp (windows_short Q₀)).comp hw))) p
   have ht0:Bill b₀ (p+1) 0 (fun i=>F (r i) _ (contour w S0 i) a-crop p (θ (r i)) (boundary N a (contour w S0 i))) := by
      apply ((hh.minus hH).plus hY').apply_eq ; filter_upwards [hk1] with i hi; rw [hi.1,hi.2]
      change _ - (F _ _ (contour w S1 i) a-F _ _ _ a)+ _=_; unfold contour; abel
   refine ⟨?_,?_⟩
   · intro j _; unfold contour; simp_rw [← to_along]; exact Bill.of_rain (revenue N M H hX hx hY hy a j) S
   have hp := ordinary_phase (p:=p+1) (simple:=simple) U K hC T w hw o a S0 C' k hC' he'
   simp_rw [hz']; exact (hp.plus ht0).apply_eq (Eventually.of_forall fun i=> by dsimp only [Function.comp_apply]; abel)
end
end YM.FVA2.GradedFar.Physical.Round
