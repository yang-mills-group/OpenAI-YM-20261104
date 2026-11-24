import YM.FVA2.Inked.Hero
/-! # Real exponential amplitudes at actual frequencies. Finitely many shots.
 Ghost directions all zero. See `Upright` and `Hall`.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked
open Function Filter Set Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical
open Lattice RG Maxwell Gen
open MS MS.Koszul MS.Plane MS.Native MS.Native.Draft MS.Cylinder.Taylor MS.Momentum MS.Theater
open MS.Color MS.Arts MS.Motif MS.Landau MS.Landau.Detect MS.Halo MS.Book MS.Heat
open Position.OpenAxis
variable {E J V X : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m n d:ℕ}{G:Gauge}
local notation "P"=> E4
local notation "L"=> Lane4 G
local notation "T"=> E × P
local notation "I"=> Complex.I
local notation "W"=> G.Color
local notation "K"=> Cfield G 0
variable {v:Axis}{i: G.ColorIndex}
lemma taste (u v:W)(i:G.ColorIndex): G.ad u v i= ∑ j:G.ColorIndex, ∑ k:G.ColorIndex, letterLie j k i * (u j*v k):= by
   nth_rw 1 [ ← color_sum u,← color_sum v ]; rw [map_sum G.ad,LinearMap.sum_apply]; simp only [ map_sum,map_smul, LinearMap.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,smul_eq_mul ]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; change v k*(u j*letterLie j k i)=_; ring
abbrev laser (i:G.ColorIndex) : W→L[ℝ]ℝ:= PiLp.proj 2 _ i
-- actual model finite
variable (B:Finset (Lane4 G))
abbrev Studio (B: Finset (Lane4 G)):= (↥B)→ ℝ
-- only actual gauge-field directions
abbrev Upright (l:Lane4 G): Prop:= ∃ a:Axis,l.1=at_g (n:=0) a l.1.2
-- w field length pure
lemma whence (w:Legs L)(h:∀ i∈w, Upright i): fieldDim wfield w=w.length:= by
   induction w with| nil=>rfl|cons i l ih=> obtain ⟨a,ha⟩:= h i ( List.mem_cons_self ); rw [field_cons,ha]; change 1 + _= _; rw [ih (fun i hi=> h i ( List.mem_cons_of_mem _ hi))] ; simp [add_comm]
def voice (w:Lane4 G)(i:Axis)(x:E4) : W:= if w.1= at_g (n:=0) i w.1.2 then flying x w.2 • baseC w.1.2 else 0
lemma voice_c (l:L)(i:Axis): ContDiff ℝ ω (voice l i) := by unfold voice; by_cases h:l.1= at_g (n:=0) i l.1.2; simp_rw [if_pos h]; exact ( flight_C _ ).smul contDiff_const; simp_rw [if_neg h]; exact contDiff_const
lemma voice_i (l:L)(i:Axis)(j:G.ColorIndex)(x:E4): voice l i x j = if l.1=at_g (n:=0) i j then flying x l.2 else 0:= by
    unfold voice; split
    next ht=> by_cases he:l.1= at_g (n:=0) i j
              · rw [ if_pos he, PiLp.smul_apply, show l.1.2=j from congrArg Prod.snd he ]; simp [baseC]
              rw [ if_neg he, PiLp.smul_apply ]; simp [ baseC, show l.1.2≠j from fun e=> he (Eq.trans ht ( congrArg ( fun j=> (at_g (n:=0) i j: K) ) e ) ) ]
    next ht=> rw [ if_neg ( show l.1≠at_g (n:=0) i j from fun H=> ht ( by rw [H] ) ) ]; rfl
-- OnlyGauge not gauge of mirrors. plays all the Real shots.
def chosen (B: Finset L): Play (Studio B) G where
   shots l := if hx: l∈B then if Upright l then Pi.single (⟨l,hx⟩: ↥B) 1 else 0 else 0
   knows := (B: Set L)
   ghost i hp:= by split_ifs with hx he; obtain ⟨a,ha⟩:= he; change parity i.1=true at hp; rw [ha] at hp; exact Bool.noConfusion hp; all_goals rfl -- inspect
-- arbitrary chosen param amplitude combines real fields. globally analytic
structure Hall (A: Play E G) (Z: E→ Sky G): Prop where
    speaks (i:Axis): ContDiff ℝ ω (fun x:T=> Z x.1 i x.2 ) -- no y ;p omit
    story (i:Axis)(x:P) : ∃ f: E→L[ℝ]G.Color, (fun y=> Z y i x)= f
    aims (i:Axis)(l:L)(x:E4): l∈A.knows→ Z (A.shots l) i x=voice l i x
    -- ink_uses for non-gauge
    offL (l:L): ¬ Upright l→ A.shots l=0

variable {A: Play E G}{Z:E→ Sky G}
def deck (B:Finset L)(i:Axis)(x:P): Studio B→L[ℝ]W:=∑ j: ↥B, ContinuousLinearMap.smulRight (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _: ↥B=>ℝ) j ) (voice j.val i x)
def reach (B:Finset L)(e:Studio B) (i:Axis)(x:P) := deck B i x e
lemma story_t : Hall (chosen B) (reach B):= by
    let X(x:P)(i:Axis):=(deck B i x); refine ⟨fun i=> ?_,fun i x=> ⟨ _,rfl ⟩,fun i l x hl=>?_,?_⟩
    · unfold reach deck; simp_rw [ _root_.sum_apply, ContinuousLinearMap.smulRight_apply ]; apply ContDiff.sum; intro j hj; refine ( ( ContinuousLinearMap.proj (ι:= (↥B) ) (R:=ℝ) (φ:=fun _: ↥B=>ℝ) j ).contDiff.comp contDiff_fst |>.smul (( voice_c (G:=G) j.val i ).comp contDiff_snd) )
    · change l∈ B at hl; unfold reach deck chosen; simp only; rw [dif_pos hl]; split
      next hp=> rw [_root_.sum_apply, Finset.sum_eq_single_of_mem ⟨l,hl⟩ (Finset.mem_univ _)]; · simp
                intro b _ ho; simp [ho]
      next hp=> rw [map_zero,voice,if_neg (fun he=> hp ⟨ _,he ⟩)]
    intro l he; unfold chosen; by_cases hx:l∈B <;> simp [hx,he]
namespace Hall
variable (h:Hall A Z)
lemma enough (w:Legs L): ∃ (E:Type) (_:NormedAddCommGroup E) (_:NormedSpace ℝ E) (A:Play E G)(Z:E→ Sky G), Hall A Z ∧ Active A w:= by classical exact ⟨ Studio w.toFinset, inferInstance, inferInstance, chosen w.toFinset, reach w.toFinset, story_t _, fun i hi=> List.mem_toFinset.mpr hi ⟩
-- key count hero property for test fields
local notation "R"=> MS.Motif.A
private lemma pen_l (F:E→L[ℝ]ℝ)(e:L→E)(w:Legs L): ink e F w=( match w with | [i]=> (( F (e i):ℝ ):ℂ) | _ => (0:ℂ) ):= by
    match w with
    | []=> simp
    | i::l=> rw [ink, show layer (e i) (⇑F)=(fun _=>F (e i)) from funext (fun x=> by unfold layer; rw [F.fderiv]), ink_const]; cases l <;> rfl
include h
lemma aura (i:Axis)(j:G.ColorIndex): Hero A 1 (fun x:E×E4=> Z x.1 i x.2 j) (R 0 G i j):= by
    let D:= laser j; refine ⟨ D.contDiff.comp ( h.speaks i ), ( Pace.here ( at_g (n:=0) i j ) ).up, fun x w hw=>?_ ⟩; obtain ⟨p,hp⟩:= h.story i x; let f:= D.comp p; rw [show (fun y:E=> Z (y,x).1 i (y,x).2 j)= f from ?_, pen_l]; swap; · funext y; exact congrArg (fun y:W=> y j) (congr_fun hp y)
    rcases w with _|⟨v,_|w⟩; exact ((mul_zero _).trans (mul_zero _).symm); swap; exact (mul_zero _).trans (mul_zero _).symm
    change I^ (1-((1:ℕ):ℤ)) * (↑( p ( A.shots v ) j ):ℂ)= _ * ( MS.Motif.leaf (n:=0) (G:=G) (at_g (n:=0) i j) [v] ); rw [ show p (A.shots v) = _ from Eq.trans (congr_fun hp (A.shots v)).symm (h.aims i v x (hw _ (by simp))), voice_i, Nat.cast_one,sub_self,zpow_zero,one_mul ]; simp only [net_cons,show net ([]:List (Lane4 G))=0 from rfl, add_zero, Motif.leaf,node1]; change (↑( if v.1=at_g (n:=0) i j then flying x v.2 else 0):ℂ)=_*(if v.1=at_g (n:=0) i j then _ else _); split <;> simp
end Hall
end YM.FVA2.Inked
