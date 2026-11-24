import YM.WilsonBridge.Substitution
import YM.MS.Swirl.Resolute

/-!
# Landau alphabet: actual Fourier conventions

The V pre-factor on the bulk vertex is precisely sum, no volume in a pinned mark.
Transfer using the same position-to-full-ambient Fourier for physical insertions as
for vertices; `lace` takes account of all midpoint phases. No assumptions on Ward/type
of vertices here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.FiniteDFT
open MS MS.Book MS.Swirl MS.Koszul MS.Cylinder MS.City MS.Latch MS.Fleet
open MS.Book.Program MS.Plane Cylinder.Lab Tone Mesh MS.Native MS.Tone MS.Landau Lattice MS.Orbit MS.Orbit.Cog
open Function Finset
open scoped BigOperators Matrix
-- generic Fourier square. momentum p is native (incl μ alias). n bound local not scaling.
variable {V : Type}[DecidableEq V][Fintype V]{G:Gauge}{n:Side}
local notation "Mod" => Mode V (Site n)
def vol (n : Side) :ℂ := n.val^4 -- ensure cast ℂ
lemma nonzero (n:Side) : vol n≠0:= pow_ne_zero _ (Bloch.side_ne n)
lemma scale_factor (n: Side): scaleZ n=(vol n)⁻¹:= by dsimp only [scaleZ,νt,vol]; push_cast; rfl
lemma brightness_eq (n:Side) : brightness n=vol n:= by rw [brightness,scale_factor,inv_inv]
lemma bill_factor (i: BH G) (p:Site n) (x:Cover):
    lace (i,Coord p)*paywave (i,Coord p) (i,x)= Bloch.cell p (wrap n x):= by
    rw [Tone.pw, rightadd, rights (Coord p) (Tone.embed x),dual_cell]
    change lace (i,Coord p)*(Bloch.cell p (wrap n x)*weightψ (i,Coord p))=_; rw [mul_left_comm (lace (i,Coord p)), mul_comm (lace (i,Coord p)), lace_,mul_one]
variable (V n)
def F : Matrix (Mode V (Site n)) (Mode V (Site n)) ℂ:= fun i j=> if i.1=j.1 then Bloch.cell i.2 j.2 else 0
def Fx : Matrix (Mode V (Site n)) (Mode V (Site n)) ℂ:= fun i j=> scaleZ n* F V n i (j.1,-j.2)
omit [Fintype V] in
lemma F_sym : (F V n).transpose=F V n:= by
    ext i j:1; simp only [F,Matrix.transpose_apply]; split_ifs with he he' he' <;> first| exact Bloch.cell_duality .. | contradiction| simp [eq_comm, *] at *
omit [Fintype V] in
lemma Fx_sym : (Fx V n).transpose=Fx V n:= by
    ext i j:1; simp only [Fx,F,Matrix.transpose_apply]; split_ifs with he he' he' <;> first| (rw [Bloch.cell_inverse,Bloch.cell_inverse,Bloch.cell_duality])| contradiction| simp [eq_comm, *] at *
lemma inv_fwd : F V n*Fx V n=1 := by
    ext ⟨i,p⟩ ⟨j,q⟩:1; simp only [F,Fx,Matrix.mul_apply,Fintype.sum_prod_type (α₁:=V),Matrix.one_apply]; by_cases he:i=j
    · subst j; rw [Finset.sum_eq_single_of_mem i (mem_univ _)]; swap; exact fun k _ h=> by simp [Ne.symm h]
      simp only [if_true]; simp_rw [Bloch.cell_inverse, Bloch.cell_duality _ q,mul_left_comm _ (scaleZ n), ← Finset.mul_sum,Bloch.orthogonal,scale_factor]; by_cases h:p=q; · rw [if_pos h,h, if_pos rfl]; exact inv_mul_cancel₀ (nonzero n)
      simp [h]
    apply (Finset.sum_eq_zero ?_).trans ((if_neg (show ¬ ((i,p)=(j,q)) from fun h=> he (congr_arg Prod.fst h))).symm); intro k _; by_cases h:i=k; · subst k; simp [he]
    simp [h]
lemma fwd_inv : Fx V n * F V n=1 := mul_eq_one_comm.mp (inv_fwd V n)
variable {V n}
omit [Fintype V] in
lemma tie_fwd (p:Sector V): Tie (field p) (field p) (fun i j:Mod=> F V n i j):= by intro i j hx; unfold F at hx; dsimp only at hx; split at hx; exact congr_arg p (by exact Eq.symm (by assumption)); contradiction
-- DFT twice (End later). no reality assumptions on Koszul row.
lemma pinned_leg (i: FixedMode G n) (j: Mode (BH G) Cover):
    F (BH G) n i (post (wrap n) j)= lace (addr i)*paywave (addr i) j:= by
    rcases i with ⟨a,p⟩; rcases j with ⟨b,x⟩; simp only [F,post,addr]; by_cases h:b=a; · subst b; rw [if_pos rfl,bill_factor]
    rw [if_neg (Ne.symm h),paywave,need id (Ne.symm h),zero_mul,mul_zero]
lemma stencilled (H:Dot G Cover) (l: Legs (FixedMode G n)) : pull (F (BH G) n) (enters n H) l= Vμ ( sleeve lace (Tone.run H) ) n l := by
    change pull _ (shown n H).val l=_; rw [pull_is_shade,shown,transport,study,Orbit.point,sleeve_here]
    simp_rw [pinned_leg]; induction l generalizing H with
    | nil=> simp [Tone.run,Orbit.stage,hook]
    | cons i l ih=>
      obtain ⟨s,hs⟩:=fromCyl H; unfold Tone.run at *
      simp only [Orbit.stage,List.map_cons,hook,List.prod_cons] at ih ⊢
      rw [ deriv_lum _ _ _ hs, deriv_lum _ _ _ hs, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro j _; rw [ih]; ring
lemma move_stamp (H:Dot G Cover) (x:Cover) (l: Legs (FixedMode G n)) : pull (F (BH G) n) (enters n ( Lab.Shift x H )) l= Φa x (net l) * Vμ ( sleeve lace (Tone.run H)) n l:= by
   rw [stencilled, Orbit.point, sleeve_here, movement, Orbit.point,sleeve_here,φ_s, be,rights ( net ( Orbit.stage l ) )]; ring
lemma rem (H:Dot G Cover) (A q:Cover) : Near.Mark_T G n A q H= pull (F (BH G) n) (enters n (Lab.Shift (A+q) H)):= by
   funext l; unfold Near.Mark_T; simp only [LinearMap.comp_apply,chase_now, Orbit.point, lodg,sleeve_here]; rw [move_stamp H, Orbit.point,sleeve_here,φ_s,φ_s,be_add]; ring
lemma through_sum (H:Dot G Cover): pull (F (BH G) n) (docket n H)= Bulk G n ( sleeve lace (Tone.run H)):= by
   let V:= FixedMode G n; funext l; have he (x:Site n): Lab.Shift x (shown n H)=shown n (Lab.Shift (Lattice.lift x) H):= by rw [show shown n _= _ from trans_shift H _ (wrap n),wrap_lift]; rfl
   change pull _ (sumHome (shown n H)).val l=_; simp_rw [total_uses,he,sum_stack,map_sum,Finset.sum_apply]; rw [bulkZ]; change (∑ i:Site n,pull _ ( enters n ( Lab.Shift ( Lattice.lift i ) H ) ) l)=_
   simp_rw [move_stamp, Φa,wrap_lift, Bloch.cell_duality _ (net l),← Finset.sum_mul]; split_ifs with hv; rw [hv,brightness_eq]; unfold vol; simp [Bloch.cell]
   rw [Bloch.sum_cell hv,zero_mul]
lemma sendBulk (b:Bool)(H: Dot G Cover) : Near.SendB G n b H= pull (F (BH G) n) ( pay b • docket n H ):= by
    change pay b • ((Bulk G n) _) =_; rw [map_smul,through_sum]; rfl
end YM.WilsonBridge.FiniteDFT
