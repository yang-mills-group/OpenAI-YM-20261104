import YM.FVA2.WilsonSource
import YM.MS.Wilson.Reflect
import YM.PertExtension.VertexSymbol
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
/-!
# MS cylinder language covers the Source.Hol and top-matrix convention

Finite-regulator local statements. `traj` keeps the parallel transports. This
matters even though it is the curvature slot at the *endpoint* which alone is
visible in `mask 1 (run ...)`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Plate
open Filter Topology Set Function MeasureTheory
open Wilson Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Koszul MS.Book
open MS.Cylinder MS.Plane MS.Cylinder.Lab MS.Cylinder.Taylor MS.Tone MS.Tone.Frame MS.Color
open RG PertExtension
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {R: Type} [AddCommGroup R] [One R]
local notation "W"=> Lattice.Cover
local notation "χ"=> Four R
variable (L : PlaqAxes)
def walkbank (d:Step) (x:χ) (i j:G.ColorIndex) : Dot G χ := if d.neg then bankSeed (d.used x).1 (d.used x).2 j i else bankSeed (d.used x).1 (d.used x).2 i j

private def legbank (d:Step) (x:χ) (i j:G.ColorIndex) (U : Rig G χ) : ℝ:= weight (d.read U x) i j

def travels (x:χ) (w:Walk) (i:G.ColorIndex) (U : Rig G χ) : ℝ :=
  α i (G.adjoint (travel U x w) (tip idRail L (stop x w) U))

private lemma travels_unroll (x:χ)(w:Walk) (d:Step)(i:G.ColorIndex) :
  travels L x (d::w) i = ∑ j:G.ColorIndex, travels L (x+d.vec) w j * legbank d x j i := by
   funext U; simp only [Finset.sum_apply,Pi.mul_apply,legbank,travels,stop,travel,Gauge.adjoint_mul,α_at]; rw [Paint.acts_all]; apply Finset.sum_congr rfl; intro j _; ring

def traj (x:χ) (w:Walk)(i:G.ColorIndex): Dot G χ := match w with
    | []=> tipSeed idRail L x i
    | d::w=> ∑ j:G.ColorIndex,couple DotFlip (traj (x+d.vec) w j) (walkbank d x j i)

lemma traj_zero (x:χ)(w:Walk)(i:G.ColorIndex): (traj L x w i).val []=0:= by
   induction w generalizing x i with
   | nil=> exact clot_zero idRail L [] x i
   | cons d w ih=> rw [traj,sum_stack,Finset.sum_apply]; exact Finset.sum_eq_zero fun j _=>by rw [coupled,nil_product,ih,zero_mul]
lemma traj_tune (x:χ)(w:Walk)(i:G.ColorIndex): Tuned (traj L x w i) 0 := by
   induction w generalizing x i with
   | nil=> exact clot_tuned idRail L [] x i
   | cons d w ih=> rw [traj]; refine Tune.sum _ fun j _=> (ih (x+d.vec) j).pair (?_ : Tuned (walkbank d x j i) 0); unfold walkbank; split <;> exact Tune_edge _ _ (gadj ..)
lemma traj_below (x:χ)(w:Walk)(i:G.ColorIndex): From (traj L x w i).val 1 := by rintro (_|i) h; exact traj_zero ..; simp at h; omega

section finite
variable [DecidableEq R][Fintype R]
private lemma legbank_run (d:Step) (x:χ)(i j:G.ColorIndex): Reads (walkbank d x i j) (legbank d x i j) := by
   unfold walkbank
   split
   · next h=> rw [show legbank d x i j= bank (d.used x).1 (d.used x).2 j i from funext fun U=> by rw [legbank,Step.read,if_pos h,weight_adj,inv_inv]; rfl]; exact bank_read ..
   · next h=> rw [show legbank d x i j= bank (d.used x).1 (d.used x).2 i j from funext fun U=> by rw [legbank,Step.read,if_neg h]; rfl]; exact bank_read ..
lemma travels_run (x:χ)(w:Walk)(i:G.ColorIndex): Reads (traj L x w i) (travels L x w i):= by
   induction w generalizing x i with
   | nil=> rw [show travels L x [] i= α i ∘ edgeSense idRail L [] x from funext fun z=>by simp only [travels,travel,stop,Gauge.adjoint_one]; rfl]; exact clot_read idRail L [] x i
   | cons d w ih=> rw [travels_unroll,traj]; exact Reads.sum _ fun j _=> (ih ..).pair (legbank_run ..)
end finite
section copies
variable {n:Side}
private lemma walkbank_wrap (x:W)(d:Step)(b:Site n)(i j:G.ColorIndex):
    transport (fun z=>wrap n z+b) (walkbank d x i j)=walkbank d (wrap n x+b) i j:= by
   rcases d with ⟨a,_|_⟩ <;> simp [walkbank,Step.used,bankSeed,onmove,sub_add_eq_add_sub]

lemma traj_copy (x:W) (w:Walk)(b:Site n)(i:G.ColorIndex): Lab.Shift b (shown n (traj L x w i))=traj L (wrap n x+b) w i:= by
   have he : ∀ x:W, transport (fun z=>wrap n z+b) (traj L x w i)=traj L (wrap n x+b) w i:= by
       induction w generalizing i with
       | nil=> exact fun x=> clot_go idRail L (fun z=>wrap n z+b) idRail (fun k j=>by simp [idRail,add_right_comm]) [] x i
       | cons d w ih=>
              intro x; simp only [traj,map_sum,transport_comes,walkbank_wrap]; refine Finset.sum_congr rfl fun j _=>?_; rw [ ih j (x+d.vec), map_add, wrap_vec,add_right_comm ]
   rw [Lab.Shift,shown]; -- maybe transport_comp
   convert! he x using 1
   · unfold transport; rw [ferry_trans]; congr 2; funext z; rw [Function.comp_apply]; simp [post,add_comm]

lemma tip_at (x:χ) (U:Rig G χ): tip idRail L x U=G.curvature (faceValue U (x,L)):= by
    unfold tip bolt₀ faceValue atCart loadC travel square idRail; simp [travel,Step.vec,mul_assoc]; rw [add_right_comm x]; simp [sub_eq_add_neg,posDir,negDir]
lemma travels_copy (x:W)(w:Walk)(b:Site n)(i:G.ColorIndex): Source.put (travels L x w i) b=travels L (wrap n x+b) w i:= by
   have he (w:Walk)(x:W): wrap n (stop x w)+b=stop (wrap n x+b) w:= by induction w generalizing x with| nil=>rfl| cons d w ih=> rw [stop,ih,stop,map_add,wrap_vec,add_right_comm]
   ext1 v; simp_rw [Source.put,Function.comp_apply,travels,tip_at,faceValue,travel_at,he]
end copies
private lemma bank_bill (x:W)(d:Step)(i j:G.ColorIndex):
    Tone.run (walkbank d x i j) []=if i=j then 1 else 0:= by 
    unfold walkbank; split
    · rw [cash_bank]; by_cases h:i=j; simp [h]; simp [h,Ne.symm h]
    exact cash_bank ..
def shine (L : PlaqAxes)(x:W) (i:G.ColorIndex)(p:LightMode G QP) : ℂ := Tone.bill p.2 (Tone.embed x)*Tone.Frame.curl L p i
lemma shine_traj (x:W)(w:Walk)(i:G.ColorIndex)(p:LightMode G QP):
    Tone.run (traj L x w i) [p]=shine L (stop x w) i p:= by
   induction w generalizing x i with
   | nil=> change run (clot idRail L [] x i) _=_; rw [clotStart, movement]; unfold shine; rw [clot,tipcost L i]; simp [net, stop]
   | cons d w ih=> rw [traj,map_sum,Finset.sum_apply]; simp_rw [small _ (traj L (x+d.vec) w _) _ (show run _ []=0 from (shade_nil _ _).trans (traj_zero ..)),bank_bill, ih]; simp [mul_ite,stop]

lemma mask_traj (x:W)(w:Walk)(i:G.ColorIndex):
 Book.mask 1 (Tone.run (traj L x w i))= Koszul.mono (shine L (stop x w) i):= by
   funext l; rcases l with _|⟨a,_|_⟩; exact (strange _ (by simp)); exact (enough [a] (by simp)).trans (shine_traj ..); apply strange; simp; omega
end YM.FVA2.Plate
