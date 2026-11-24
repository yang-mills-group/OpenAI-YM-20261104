import YM.SchemeConversionRG11.FirstW.Trice.Catch
import YM.SchemeConversionRG11.FirstMS.Triad.Colors
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS
open scoped ContDiff BigOperators Classical Topology
variable {T:Itinerary}{G:Gauge}{X:Type} {S:Set E4}{c:ℕ→Side} {A B:Sight T G} {p q:Axis→ E4→G.Color}
def landingL (T:Itinerary)(K:Set E4)(f:Sight T G)(p:Axis→E4→G.Color):=∀ i:Axis,Meets T K (stalkH T f i) (p i)
def mapW (p:Axis→ E4→ G.Color)(y:E4): Field4 G:=fun e=>p e.2 y
lemma looksV (h: landingL T S A p)(i:Step): Meets T S (peakC T A i) (fun v=> boardAt (0:Cover) i (mapW p v)):= by
 rw [lookC]; let L:= flareL i; simp only [board_spin]; exact ((h i.dir).east _).move (fun x:G.Color=> L • x) (continuous_const_smul _)
lemma walksV (h:landingL T S A p)(t:Walk)(x:Cover): Meets T S (fun i y=> rail y t (A i)) (fun v=> rail x t (mapW p v)):= by
 induction t generalizing x with
 | nil=> simp only [rail,LinearMap.zero_apply]; exact Meets.nil
 | cons i t ih=>
   have H: Meets T S (fun j y=> rail (y+i.vec) t (A j)) (fun v=>rail (x+i.vec) t (mapW p v)):=by simpa only [wrap_vec] using (ih (x+i.vec)).east i.vec
   have he (v): boardAt x i (mapW p v)=boardAt (0:Cover) i (mapW p v):= by rw [board_spin,board_spin]; rfl
   simp only [rail,LinearMap.add_apply,he]; exact (looksV h i).plus H
lemma bentV (h:landingL T S A p)(e:landingL T S B q)(w:Walk)(x:Cover): Meets T S (fun i y=>swerve y w (A i) (B i)) (fun v=>swerve x w (mapW p v) (mapW q v)):=by
 induction w generalizing x with
 | nil=> simp only [swerve, LinearMap.zero_apply]; exact Meets.nil
 | cons i w ih=>
   have ht: Meets T S (fun j y=>swerve (y+i.vec) w (A j) (B j)) (fun v=>swerve (x+i.vec) w (mapW p v) (mapW q v)):=by simpa only [wrap_vec] using (ih (x+i.vec)).east i.vec
   have hm: Meets T S (fun j y=> rail (y+i.vec) w (B j)) (fun v=>rail (x+i.vec) w (mapW q v)):=by simpa only [wrap_vec] using (walksV e w (x+i.vec)).east i.vec
   have he (v): boardAt x i (mapW p v)=boardAt (0:Cover) i (mapW p v):= by rw [board_spin,board_spin]; rfl
   obtain ⟨L,H⟩:= doubles G.ad
   simp only [swerve_eq,he,←H]; apply Meets.plus (g:=fun j y=>swerve (y+i.vec) w (A j) (B j)) _ ht
   exact (looksV h i).price hm (fun a b=>L a b) (show Continuous (uncurry (fun a b=> L a b)) from (L.continuous.comp continuous_fst).clm_apply continuous_snd)
def pitch (p q:Axis→E4→ G.Color)(i j:Axis)(v:E4):= G.ad (p i v) (q j v)-G.ad (p j v) (q i v)
def claw (T:Itinerary)(A B:Sight T G)(i j:Axis): Hall T G.Color:= fun s x=> spire G x (square i j) (A s) (B s)
lemma pitches (p q:Axis→ E4→ G.Color)(i j:Axis)(v:E4) (x:Cover): spire G x (square i j) (mapW p v) (mapW q v)= pitch p q i j v:= by
 -- diagonal, skip direct simplex
 have eh (p:Axis→E4→ G.Color)(t:E4): spire G x (square i j) (mapW p t) (mapW p t)= (2:ℝ) • G.ad (p i t) (p j t) := by
   unfold spire
   simp only [LinearMap.add_apply,LinearMap.smul_apply, LinearMap.flip_apply,← two_smul ℝ, smul_smul]; norm_num
   simp only [Lattice.square,swerve_eq, rail, LinearMap.add_apply,board_spin]; simp only [mapW,posDir,negDir,flareL];simp only [↓reduceIte,Bool.false_eq_true,one_smul,neg_smul,swerve,LinearMap.zero_apply]
   simp only [map_zero,map_add, map_neg,LinearMap.neg_apply,ad_diag0,neg_zero,zero_add,add_zero,neg_neg]; rw [ad_for (p j t) (p i t),two_smul]; abel
 have ht:mapW (p+q) v=mapW p v+mapW q v:=rfl
 have H:= eh (p+q) v; rw [ht] at H; simp only [map_add,LinearMap.add_apply, spire_comm (A:=mapW q v) (B:=mapW p v), Pi.add_apply] at H
 rw [eh p v,eh q v,ad_for (q i v) (p j v)] at H; apply smul_right_injective _ (by norm_num : (2:ℝ)≠0); unfold pitch; simp only [two_smul] at *; apply sub_eq_zero.mp; have hh:=sub_eq_zero.mpr H; exact (by convert! hh using 1; abel)
lemma clawV (h:landingL T S A p)(e:landingL T S B q)(i j:Axis): Meets T S (claw T A B i j) (pitch p q i j):= by
 unfold claw; rw [show pitch p q i j=(fun v=> spire G (0:Cover) (square i j) (mapW p v) (mapW q v)) from funext fun _=>(pitches ..).symm]; simp only [spire,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.flip_apply]; exact Meets.move ((bentV h e _ 0).plus (bentV e h _ 0)) (fun x:G.Color=> (1/2:ℝ) • x) (continuous_const_smul ..)
end YM.RG11.FirstW
