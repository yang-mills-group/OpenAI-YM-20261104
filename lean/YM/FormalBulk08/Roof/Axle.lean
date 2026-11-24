import YM.FormalBulk08.Roof.Grade
import YM.FormalBulk08.Rial.Tone

/-! Column tower algebra. Cutoffs change with *same* profile at held root; a products-on-sources API independent of cutoffs. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Roof
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J: Type*} {G:Gauge}{d k m l u e r j D:ℕ}{s:Signed}{x:Loc G 1}{P:Patch}{σ A:ℝ}
abbrev Tilework (F:Frame G d) := Pennants (Letter F)
abbrev Plaza (F:Frame G d)(D:ℕ) := Letter F → Anthem D G
variable {F:Frame G d}{U T: Anthem D G}{Y:Plaza F D}{w:I→ℕ}{L : Side}
lemma son_round (h : Wade x T l) (hu : Wade x T u)(hp : Wade x U l)(he:Wade x U u)(hv:Son T U l s): Son T U u s:= by
   intro n p; by_cases h':l≤u
   · rw [← banner_rise h h',← banner_rise hp h']; exact hv n p
   rw [banner_rise hu (le_of_not_ge h'),banner_rise he (le_of_not_ge h')]; exact hv n p
lemma clef_youth (h:Clef x T l)(ht:∀ p,Young (T p) m): Clef x T m := by have hv:=show Wade x T m from ⟨ht,h.fare.2⟩; exact ⟨h.toIsLinearMap,hv,son_round h.fare hv h.fare hv h.ward⟩
lemma clef_through (h:Clef x T l)(he:l≤m):Clef x T m:= clef_youth h (h.fare.through he).1
lemma ring_yield (p:Pence)(h:Wade x T l) (h':∀ i,m+i < l→PowerSeries.coeff i p=0) v : Young ((launch p T) v) m:= by
   intro e r he; by_contra hp; apply he; unfold launch surf; refine Finset.sum_eq_zero fun i hi=>?_; rw [Finset.mem_antidiagonal] at hi; by_cases hu: T v i.2 r=0
   · rw [hu,smul_zero]
   have hh:= h.1 v i.2 r hu; rw [h',zero_smul]; unfold Yield at *;omega
lemma launch_cut (p:Pence)(h:Clef x T l) (h':∀ i,m+i<l→PowerSeries.coeff i p=0) : Clef x (launch p T) m:= clef_youth (h.launch p) (ring_yield p h.fare h')
lemma void_launch (Y:Anthem D G): launch 0 Y=0:= by rw [←map_zero C,launch_C,zero_smul]
lemma laze_void (p:Pence): launch p (0:Anthem D G)=0:= by funext x e r; simp [launch,surf]
lemma launch_from {I:Type*} (V:Finset I)(p:I→ Pence)(Y: Anthem D G): launch (∑ i∈V,p i) Y = ∑ i∈V,launch (p i) Y:=by induction V using Finset.induction with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty,void_launch]
   | insert i K h ih=>rw [Finset.sum_insert h,Finset.sum_insert h, launch_add,ih]
lemma launch_ship {I:Type*} (V:Finset I)(Y:I→ Anthem D G)(p: Pence): launch p (∑ i∈V,Y i) = ∑ i∈V,launch p (Y i):=by induction V using Finset.induction with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty,laze_void]
   | insert i K h ih=>rw [Finset.sum_insert h,Finset.sum_insert h, launch_plus,ih]

-- Y matrix by right action. General alphabets. Every map applies even
-- on unequally weighted columns (cost separately).
section
variable [Fintype I]
def larch (Y: I→ Anthem D G)(T: Matrix I J Pence) : J→Anthem D G:= fun j => ∑ i:I, launch (T i j) (Y i)
variable {X:Type*}
lemma larch_circuit [Fintype J](Y:I→ Anthem D G)(T:Matrix I J Pence)(W:Matrix J X Pence) : larch (larch Y T) W=larch Y (T*W):= by
   funext x; unfold larch; simp_rw [launch_ship,launch_launch, Matrix.mul_apply,launch_from];rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun j _=> by rw [mul_comm]
lemma larch_unit [DecidableEq I](Y:I→ Anthem D G) : larch Y (1:Matrix I I Pence)=Y := by
    funext x; unfold larch; rw [Finset.sum_eq_single x,Matrix.one_apply_eq,launch_one]; intro i _ he;rw [Matrix.one_apply_ne he,void_launch];simp
lemma larch_cleared {T:Matrix I J Pence}{Y:I→ Anthem D G}(w:I→ℕ)(k:J→ℕ)(ht:∀ i j e,k j+e<w i→PowerSeries.coeff e (T i j)=0)(h:∀ i,Clef x (Y i) (w i)) :∀ j, Clef x (larch Y T j) (k j):= fun j=> Clef.sum Finset.univ _ (fun i _=> launch_cut (T i j) (h i) (ht i j))
end

lemma echo_zero (F:Frame G d) : echo F (0:Anthem D G) = 0:= by funext i; ext1 n; simp [echoline,chalk_void]
lemma echo_tally (F:Frame G d)(S:Finset I)(Y:I→ Anthem D G)(h:∀ i ∈S,Wade x (Y i) l)(j:Letter F) : Wade x (∑ i∈S,Y i) l ∧ echo F (∑ i∈S,Y i) j=∑ i∈S, echo F (Y i) j:= by
    induction S using Finset.induction with
    | empty=>simp only [Finset.sum_empty]; exact ⟨wade_zero,congr_fun (echo_zero F) _⟩
    | insert i s he ih=> obtain ⟨ht,H⟩:= ih (fun i hi=> h i (Finset.mem_insert_of_mem hi)); rw [Finset.sum_insert he,Finset.sum_insert he,etched_add F (h i (Finset.mem_insert_self ..)) ht,Pi.add_apply,H]; exact ⟨(h i (Finset.mem_insert_self ..)).add ht,rfl⟩
def pantry (F:Frame G d)(Y : I→ Anthem D G) : Matrix (Letter F) I Pence:= fun i j=> echo F (Y j) i
lemma pantry_handle [Fintype I]{Y : I→ Anthem D G}(F:Frame G d)(T:Matrix I J Pence)(h:∀ i,Wade x (Y i) l) : pantry F (larch Y T) = pantry F Y*T:= by
    ext1 i j; rw [Matrix.mul_apply]; unfold pantry larch; rw [show echo F (∑ k:I,launch (T k j) (Y k)) i=_ from (echo_tally F Finset.univ _ (fun k _=> (h k).launch (T k j)) i).2]; apply Finset.sum_congr rfl; intro k _; rw [etched_launch F _ (h k),mul_comm] -- ext i j issue
end YM.FormalBulk08.Roof
