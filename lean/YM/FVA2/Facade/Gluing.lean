import YM.FVA2.Facade.Timber
/-!
# Gluing the kept fields at Bottom

This is genuine orbit Haar in the `Used` frame. See `stipulate` for the price,
and `truePrice` for the $t$-dependent version.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb
open scoped Classical Topology BigOperators ContDiff
variable {G: Gauge} {c f n:Side} {L:Fabric G n}

-- board to all root-collapsed links, followed by sincere pullbacks
variable (T:Cloth L)
 def door (x:Warm T→ G.El): Used L→ G.El:= (fir T).board (fun i=> x ((leeway T).symm i))
lemma door_cont : Continuous (door T):= (fir T).board_cont.comp (continuous_pi (fun _=> continuous_apply _))
lemma door_one : door T 1=1:= (fir T).board_one

lemma door_tree (x) (i:Used L)(h:(fir T).Branch i) : door T x i=1:= by simp [door,Loom.Truss.board,Loom.Truss.stitch,h]
lemma door_loop (x) (i:(fir T).Bulk): door T x i.val= x ((leeway T).symm i):= by simp [door,Loom.Truss.board]
section
variable {S:StepData c f}{H:S.patch.Branches S.kernel G}{hf:Even f.val}{t:S.Choices}{U:Fabric G c}
variable {P:Inside S.ratio}{C:Cloth U}
local notation "Γ"=> layer S H t hf U
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "A"=> fir (T0)
local notation "e"=>credit (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "κ"=>leeway T0
lemma leeway_in (x:Index S P):(κ) (Sum.inl x)= graft P (Sum.inl x):= rfl
lemma leeway_out (x:Warm C) :(κ) (Sum.inr x)=graft P (Sum.inr ((leeway C) x)):=rfl
lemma enlisted (i:Used U)(x:Warm T0→ G.El) : door T0 x (Sum.inr i)= door C (fun i=> x (Sum.inr i)) i:= by
 by_cases h:(fir C).Branch i
 · have he:(A).Branch (Sum.inr i):= (sprig_later P (fir C) i).mpr h
   exact (door_tree T0 x _ he).trans (door_tree C _ i h).symm
 let y:= ((leeway C).symm ⟨i,h⟩); let a:= graft (H:=H) (hf:=hf) (t:=t) P (Sum.inr (Subtype.mk i h));
 have ha : a = (κ) (Sum.inr y):= by rw [leeway_out,show (leeway C) y = _ from (leeway C).apply_symm_apply _];
 erw [door_loop T0 x a,door_loop C (fun i=>x (Sum.inr i)) ⟨i,h⟩, ha, Equiv.symm_apply_apply]

lemma enlisted_exp (i:OEdge f)(x w) : door T0 (expLinks G _ (e (x,w))) (Sum.inl i) = expLinks G _ (extend P x) i:= by
 let M:= door T0 (expLinks G _ (e (x,w)))
 by_cases h:P.Innate i
 · have he:(A).Branch (Sum.inl i):= (sprig_now P (fir C) i).mpr h
   erw [expLinks,show (OpenSlots.extend P x) i=0 from (by simp [OpenSlots.extend,h])]; simpa using! door_tree T0 (expLinks G _ (e (x,w))) _ he
 let j: Index S P:= ⟨i,h⟩
 have hh : (OpenSlots.extend P x) i=x j:= by simp [OpenSlots.extend,h]; rfl
 unfold expLinks; rw [hh]; unfold door Loom.Truss.board; let g(i):=(expLinks G _ (e (x,w))) ((κ).symm i)
 erw [(A).stitch_bulk 1 g (κ (Sum.inl j))]; unfold g; rw [Equiv.symm_apply_apply]; rfl
lemma attend_future (x w u) : future S H t hf U (rear Γ u (door T0 (expLinks G _ (e (x,w)))))= rear U u (door C (expLinks G _ w)):= congr_arg (rear U u) (funext (fun i=> enlisted (P:=P) (t:=t) (H:=H) (hf:=hf) i (expLinks G _ (e (x,w)))))
end
lemma attend_main (x y): L.principal (rear L (expLinks G _ y) (door T (expLinks G _ x)))= expLinks G _ (line T (x,y)) := by
 cases T with
 | floor=> rfl
 | @inLayer c f S H t hf L P C=>
    obtain ⟨⟨x,w⟩,rfl⟩:= (credit (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)).surjective x; rw [lined]; exact funext (fun i=> enlisted_exp i x w)
lemma attend_valve {n:Side}{L: Fabric G n}(T:Cloth L)(i:L.Cost) (x y) : L.regional (rear L (expLinks G _ y) (door T (expLinks G _ x))) i= valve T i (x,y):= by
 cases T with
 | floor=> exact Empty.elim i
 | @inLayer c f S H t hf L P C=>
    let T0:=Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C; let e:= credit (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
    obtain ⟨⟨x,w⟩,rfl⟩:= e.surjective x; change Option L.Cost at i; cases i with
    | none=>
       rw [Fabric.regional]; simp only [Option.elim_none]
       erw [attend_main, lined, attend_future,attend_main];
       rw [valve]; simp only [Option.elim_none]; erw [comp_apply, arrived]; rfl
    | some i=>
       rw [valve,Fabric.regional]; simp only [Option.elim_some]; dsimp only [Function.comp_apply]
       erw [attend_future, descending]; exact attend_valve C i w y
termination_by structural T

lemma stipulate (i:L.Accounts)(x y): L.price (rear L (expLinks G _ y) (door T (expLinks G _ x))) i= Facade.rate T i (x,y):= by
 cases i with
 | some i=> exact attend_valve T i x y
 | none=> unfold Fabric.price; rw [Option.elim_none, attend_main]; rfl

 def committed (y: Flats G (Bottom L)) (g:ℝ)(x:Warm T→ G.El) : L.LinksOn:= rear L (expLinks G _ (g • y)) (door T x)
 def front (w:L.Accounts→ℝ→ℝ)(y: Flats G (Bottom L))(g:ℝ)(x:Warm T→ G.El) : ℝ:= L.spend (fun i=> w i g) (committed T y g x)

-- This is exact all g parameter for this surface. `T` captures all pinned tree Choices.
lemma truePrice (w:L.Accounts→ℝ→ℝ)(y:Flats G (Bottom L))(r:ℝ)(x:Panel T) : Facade.raise (Facade.rate T) w y (r,x)= r^2+ front T w y r (expLinks G _ x):=by
 unfold Facade.raise; rw [Pi.add_apply,Finset.sum_apply]; apply congr_arg (r^2+·); exact Finset.sum_congr rfl fun i _=> congr_arg (w i r * ·) (stipulate T i x (r • y)).symm
end YM.FVA2.Facade
