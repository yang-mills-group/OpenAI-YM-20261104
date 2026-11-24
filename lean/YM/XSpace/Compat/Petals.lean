import YM.XSpace.Compat.Ride
import YM.Further.FREE_COVARIANCE_KP.KP.Petals
import YM.Maxwell.Curls

/-! Additive compatibility closure from pinned Oct15 ancestry.
Current baseline definitions are reused; extracted declaration text is unchanged.
Prepared for independent checking; no successful build is claimed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Exterior Lattice Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace

def legendary (a b : PA) := Maxwell.bareCurl a.val.1 a.val.2 b.val.1 b.val.2

def decree (A B : List Axis) (a b:PA) (x : E4) : ℝ := (-1)^B.length * ride B (ride A (legendary a b)) x
-- (-1)^B.length uses ℝ

private lemma corner (a : PA) (q : Axis → ℂ) (v : X1→ℂ) :
    (wedge 1 q *ᵥ v) (plaquette a) = q a.val.1 * v (coord a.val.2)-q a.val.2 * v (coord a.val.1) := by
  let b := a.val.1; let d := a.val.2; have hb : b<d := a.property
  let F := plaquette a
  have hh : F.val={b,d} := rfl
  unfold wedge; rw [Matrix.sum_mulVec]; simp_rw [Matrix.smul_mulVec]; rw [Finset.sum_apply]
  change ∑ i, q i * ((left ℂ 1 i)*ᵥv) F=_
  rw [← Finset.sum_subset (Finset.subset_univ ({b,d}:Finset Axis)),Finset.sum_insert (by simp [hb.ne]), Finset.sum_singleton]
  · have hs : b∈F.val := hh ▸ Finset.mem_insert_self ..
    have ht : d∈F.val := by simp [hh]
    have hb' : remove b F hs=coord d := by ext i; by_cases he:i=b <;> simp [coord,remove,hh,he,hb.ne]
    have hd' : remove d F ht=coord b := by ext i; by_cases he:i=d <;> simp [coord,remove,hh,he,hb.ne']
    simp_rw [eliminate]; rw [dif_pos hs,dif_pos ht,hb',hd']
    rw [parity,parity,pre,pre]; simp [hh,Finset.filter_insert,Finset.filter_singleton,hb,hb.not_gt]; rfl
  intro i _ h; rw [eliminate,dif_neg (show i∉F.val from hh ▸ h),mul_zero]
end YM.XSpace.Compat.KP

namespace YM.Further.FreeCovariance.KP.Matches
open YM.XSpace.Compat.KP
open Filter Set Function Metric Complex MeasureTheory Exterior Lattice Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {n : ℕ} {f f' : E4→ℂ} {g g' : E4→ℝ}

lemma basic (A : List Axis) : Matches n (fun p=>bill turned A p * water p) (ride A Maxwell.Green) := by
  refine ⟨(skin_story A).1,?_⟩
  obtain ⟨C,hC,H⟩ := riding_funds A n
  refine ⟨C,hC,fun p hp=> ?_⟩
  rw [retract_skin _ (norm_pos_iff.mp (zero_lt_one.trans_le hp))]
  rw [sub_sub_cancel_left,norm_neg]
  exact H p hp

lemma join (h : Matches n f g) (ht : Matches n f' g') : Matches n (f+f') (g+g') := by
  refine ⟨h.serves.join ht.serves,?_⟩; obtain ⟨C,hC,H⟩:=h.rate; obtain ⟨B,hB,K⟩:=ht.rate; refine ⟨C+B,by positivity,fun x hx=>?_⟩
  unfold retract
  rw [meal_sum h.serves.delivered ht.serves.delivered,Pi.add_apply,Complex.ofReal_add,mul_add]
  change ‖(retract _ _+retract _ _)-(_+_)‖ ≤ _
  rw [add_sub_add_comm,add_mul]
  exact (norm_add_le ..).trans (add_le_add (H x hx) (K x hx))

lemma scale (h : Matches n f g) (t:ℝ) : Matches n ((t:ℂ) • f) (t • g) := by
  refine ⟨h.serves.scale (t:ℂ),?_⟩; obtain ⟨C,hC,H⟩:=h.rate; refine ⟨‖(t:ℂ)‖*C,by positivity,fun x hx=>?_⟩
  rw [show retract ((t:ℂ) • f) x=(t:ℂ)*retract f x by unfold retract feed; simp only [Pi.smul_apply, smul_eq_mul]; simp_rw [mul_left_comm (song x _) (↑t:ℂ),integral_const_mul]; ring, Pi.smul_apply,smul_eq_mul, Complex.ofReal_mul,← mul_sub,norm_mul,mul_assoc]
  gcongr
  exact H x hx

lemma fall (h : Matches n f g) (ht : Matches n f' g') : Matches n (f-f') (g-g') := by
  have hh := ht.scale (-1); rw [Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul,neg_one_smul] at hh; simp only [sub_eq_add_neg]; exact h.join hh

lemma vacate : Matches n (fun _=>0) (fun _=>0) := ⟨Profit.owned,0,le_refl _,fun x _=> by simp [retract,feed]⟩
end YM.Further.FreeCovariance.KP.Matches

namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Exterior Lattice Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace

private def unfold4 {F : Type} [Sub F] (a b : PA) (f : Axis→Axis→Axis→Axis→F) : F :=
  let (i,j) := a.val; let (k,l) := b.val
  (f i l k j-f i k l j) - (f j l k i-f j k l i)

private def topL (A : List Axis) (i j k l : Axis) (p:E4) : ℂ :=
  if k=l then bill turned ([j,i]++A) p*water p else 0

private def botL (i j k l : Axis) : E4→ℝ :=
  if k=l then ride [j,i] Maxwell.Green else 0

private def banner (B : List Axis) := (-1:ℝ)^B.length

private lemma petal_bill (B : List Axis) (p:E4) : star (bill turned B p)= (↑(banner B):ℂ)*bill turned B p := by
  induction B with
  | nil => simp [bill,banner]
  | cons b B ih =>
    rw [show bill turned (b::B) p=turned p b * bill turned B p from rfl,star_mul,ih]
    simp [banner,pow_succ,turned_at]; ring

def stalk (A B : List Axis) (a b : PA) (p:E4) := breeze 1 p * pearls A B p (plaquette a) (plaquette b)

private lemma petal_scope (A B : List Axis) (a b : PA) : stalk A B a b=(↑(banner B):ℂ) • unfold4 a b (topL (A++B)) := by
  funext p; unfold stalk pearls pearl; let T := wedge 1 (turned p)
  let i := a.val.1; let j := a.val.2; let k := b.val.1; let l := b.val.2
  have he : (T*Tᴴ) (plaquette a) (plaquette b) = turned p i * star (T (plaquette b) (coord j)) - turned p j * star (T (plaquette b) (coord i)) := corner a (turned p) (fun i=>Tᴴ i (plaquette b))
  have hb (n:Axis) : T (plaquette b) (coord n)= turned p k*(if l=n then 1 else 0) - turned p l*(if k=n then 1 else 0) := by
    have hh := corner b (turned p) (Pi.single (coord n) 1)
    simpa only [mulVec_single_one,Pi.single_apply,coord_iff,Matrix.col, Matrix.transpose_apply,T,k,l] using hh
  rw [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]; simp only [Matrix.smul_apply, Pi.smul_apply,unfold4]
  simp only [smul_eq_mul]
  rw [petal_bill]
  simp only [show wedge 1 (turned p)=T from rfl,he,hb,topL,bill,banner,water,List.map_append,List.prod_append,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,Pi.sub_apply]
  -- `let` axes before split
  have hc (x : E4) (a : Axis) : star (turned x a)= -turned x a := by simp [turned_at]
  simp only [i,j,k,l,star_sub,star_mul,hc]
  have hd (b c:Axis) (X Y:ℂ) : (if b=c then X*Y else 0)=(if b=c then 1 else 0)*X*Y := by split_ifs <;> simp
  have hh (b c:Axis) : star (if b=c then (1:ℂ) else 0)=(if b=c then 1 else 0) := by split_ifs <;> simp
  simp only [hd,hh]; ring

private lemma petal_answer {x:E4} (hx : x≠0) (A B : List Axis) (a b : PA) : decree A B a b x=
    (banner B • unfold4 a b (fun i j k l => ride (A++B) (botL i j k l))) x := by
  have he : legendary a b =ᶠ[𝓝 x] unfold4 a b botL := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show x∈({0}ᶜ:Set E4) from hx)] with y hy
    simp only [legendary, unfold4,botL, Maxwell.bareCurl,Pi.sub_apply, Maxwell.Bare.opp_grad hy]; split_ifs <;> rfl
  have ht (i j k l : Axis) : ContDiffAt ℝ ∞ (botL i j k l) x := by unfold botL; split_ifs; exact ride_smooth _ (Maxwell.freeSmooth hx); exact contDiffAt_const
  unfold decree; rw [ride_join,(ride_germ (A++B) he).eq_of_nhds]; unfold unfold4; dsimp only -- Pi addition explicit
  rw [ride_sub (A++B) (?_) (?_),ride_sub _ (ht _ _ _ _) (ht _ _ _ _),ride_sub _ (ht _ _ _ _) (ht _ _ _ _)]; rfl
  all_goals exact (ht _ _ _ _).sub (ht _ _ _ _)

theorem scent (n) (A B : List Axis) (a b : PA) : Matches n (stalk A B a b) (decree A B a b) := by
  have ht (i j k l:Axis) : Matches n (topL (A++B) i j k l) (ride (A++B) (botL i j k l)) := by
    unfold topL botL; split_ifs
    · rw [ride_join]; exact Matches.basic _
    rw [ride_nil]; exact Matches.vacate
  have h : Matches n (stalk A B a b) (banner B • unfold4 a b (fun i j k l=> ride (A++B) (botL i j k l))) := by
    rw [petal_scope]; unfold unfold4; dsimp only; exact Matches.scale (Matches.fall (Matches.fall (ht ..) (ht ..)) (Matches.fall (ht ..) (ht ..))) _
  refine ⟨h.serves,?_⟩; obtain ⟨C,hC,H⟩ := h.rate; refine ⟨C,hC,fun x hx=>?_⟩; rw [petal_answer (norm_pos_iff.mp (zero_lt_one.trans_le hx))]; exact H x hx

end YM.XSpace.Compat.KP
end
