import YM.FVAAlt2.Bill

/-!
# all vertices, determinant and scalar weight at the original bare coupling

Signs as stored in `Kernel.pull` and in ``slice``. Use analytic germs in `Chart`
but S2 has been removed from `pureEnergy`. The analytic Wilson/report prescriptions
keep explicitly their f-independent leading factors (show exp + rank parity matters).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open SchemeRG11.Sway Lattice Function MS MS.Book MS.Koszul MS.Native MS.Native.Wilsonian MS.Cylinder MS.Cylinder.Taylor
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Cylinder.Lab Finset Filter Topology Pert.Orb
open scoped Classical ContDiff PowerSeries
variable {G:Gauge}{n:Side}{ι κ:Type}[Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A : Module.Basis ι ℝ (Land G n))(b: Module.Basis κ ℝ (ScalarGhost G n))
local notation "E"=> Com (isOdd (ι:=ι) (κ:=κ))
local notation "K"=> propagator (κ:=κ) A
local notation "B"=> Bos ι
local notation "T"=> PowerSeries (Com (isOdd (ι:=ι) (κ:=κ)))
local notation "𝑩"=>PowerSeries (Bos ι)
local notation "V"=> Land G n
local notation "p"=> isOdd (ι:=ι) (κ:=κ)
local notation "L"=>embeddingM A b
local notation "𝒥"=>ink (dirA4 (κ:=κ) A)
local notation "cB"=> PowerSeries.constantCoeff (R:=Bos ι)
local notation "c0"=> PowerSeries.constantCoeff (R:=E)
local notation "ℳ"=> PowerSeries.coeff (R:=E)
local notation "f!"=> Com.forget p
set_option linter.unusedSectionVars false

lemma mask_pair {J:Type}{q:Sector J}{F:Raw J ℂ} (n:ℕ) {c:ℤ}(h:rank c F)(Y:Raw J ℂ) : mask (n+c) (product q F Y) = product q F (mask n Y) := by
  have he: From F c:= fun l hl=> h l (by rw [mod_int]; exact ne_of_lt hl)
  have hY: From Y 0:= fun l hl=> False.elim (by omega)
  have ht:= Book.pairLevel («p»:=q) n he hY
  unfold rankLevel at ht; rw [add_zero] at ht; rw [← ht,Finset.sum_eq_single_of_mem (0,n) (by simp)]; · simp only [Nat.cast_zero,zero_add,add_zero,(rank_hat _).mp h]
  rintro ⟨i,j⟩ hu hx; simp only; rw [rank_off h ?_,map_zero]; rfl
  intro eq; simp only [mem_antidiagonal] at hu; exact hx ( by congr! <;> omega ) -- puzzle

lemma bob_inside (f : V→ℝ)(hf:germ f)(i:ℕ): (Bos.up (κ:=κ) (Bos.bob A f hf i)).val = mask i (𝒥 f):= by rw [Bos.up_v]; change pull (Bos.projVec ι κ) (mask i (ink A f))=_; rw [pull_mask,Bos.launch (fun i:ι=> A i) f hf]; rw [show dirA4 (κ:=κ) A=Sum.elim A (fun _=>0) from funext (Sum.rec (fun _ => rfl) (fun _ => rfl))]
lemma initial_bob (f:V→ℝ)(h:germ f): Bos.bob A f h 0= Com.piece (f 0:ℂ):= by
  apply Subtype.ext; funext l; rw [Com.piece_val]; change mask 0 _ l=_; cases l with| nil=> exact enough [] rfl| cons i l=> exact strange _ (by simp; omega)

def hrLog (a: Land G n):= Real.log (Jacob a.val)
lemma hJac : germ (fun x:Land G n=> Jacob x.val):= (show ContDiffAt ℝ ω Jacob (g0 G n 0) from (g0 G n).map_zero.symm ▸ Pert.Orb.jacobian_smooth).comp (f:=g0 G n) 0 ((ContinuousLinearMap.contDiff (𝕜:=ℝ) («E»:=Land G n) (F:=Potential G n) (g0 G n)).contDiffAt)
lemma hLog : germ (hrLog (G:=G) (n:=n)):= (hJac (G:=G) (n:=n)).log (by simp)
lemma barTree (i j:κ): germ (fpLetter b i j):= fp_germ4 .. -- η

def priceMat : 𝑩:= PowerSeries.mk (fun i=> if i=0 then 0 else -(Bos.bob A LAND LANDsmooth (i+2)))
def hrMat : PowerSeries (Bos ι):= Bos.seriesInk (X:=Land G n) A (hrLog (G:=G) (n:=n)) hLog
def FPInk (i j:κ): 𝑩:= -Bos.seriesInk A (fpLetter b i j) (barTree b i j)
def radiant : Matrix κ κ (PowerSeries (Bos ι)):= Matrix.of (FPInk A b) -1
-- use column-oriented body
lemma piece_z : Com.piece (0:ℂ) = (0:B) := by rw [← Com.alg_piece,map_zero]
lemma price0 : cB (priceMat A)=0:= by simp only [←PowerSeries.coeff_zero_eq_constantCoeff,priceMat,PowerSeries.coeff_mk,if_true]
lemma hr0 : cB (hrMat A)=0:= by rw [← PowerSeries.coeff_zero_eq_constantCoeff,hrMat,Bos.seriesInk,PowerSeries.coeff_mk, initial_bob]; simp [hrLog, piece_z]
lemma radiant0 (i j:κ): cB (radiant A b i j)=0:= by
  simp only [radiant,FPInk,Matrix.of_apply,Matrix.sub_apply, Matrix.one_apply,map_sub,map_neg, ←PowerSeries.coeff_zero_eq_constantCoeff_apply,Bos.seriesInk, PowerSeries.coeff_mk,initial_bob,fp_flat,← Com.alg_piece]; by_cases h:i=j <;> (simp [h]; rw [← Com.alg_piece]; simp only [map_neg,map_zero,map_one,neg_neg,sub_self])
lemma gravity0 (i j:κ): c0 (Bos.upS (radiant A b i j))=0:= by rw [←PowerSeries.coeff_zero_eq_constantCoeff,Bos.upS,PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,radiant0,map_zero]

lemma ghost_mask (i:ℕ) : mask (i+2:ℤ) (ghostAction A b)=∑ j:κ,∑ k:κ, product p (Glue.pairG ι j k).val (-(Bos.up (κ:=κ) (Bos.bob A (fpLetter b j k) (barTree ..) i)).val):=by
  unfold ghostAction; rw [map_sum]; apply sum_congr rfl; intro j _; rw [map_sum]; apply sum_congr rfl; intro k _; rw [bob_inside, Glue.anti, ← Koszul.times_assoc]
  simp_rw [Glue.psi, Glue.theta,map_neg, LinearMap.neg_apply,neg_neg]
  rw [mask_pair i ?_]; exact (show rank 1 (atLetter (antigh (ι:=ι) j) (R:=ℂ)) from Rails.letter _ (v:=fun _=>1)).product (show rank 1 (atLetter (gh (ι:=ι) k) (R:=ℂ)) from Rails.letter _ (v:=fun _=>1)) -- placeholder syntax

def fixedAct : T:= Bos.upS (priceMat A+hrMat A) + ∑ j:κ, Glue.debit ((radiant A b).map (Bos.upS (κ:=κ))) j
lemma fixed0: c0 (fixedAct A b)=0:= by
  rw [fixedAct,map_add (c0), map_sum]; have ht:∀ j k,c0 (((radiant A b).map (Bos.upS (κ:=κ))) j k)=0:=gravity0 A b; rw [Finset.sum_eq_zero (fun i _=>?_),add_zero]; swap; · rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact Glue.debit0 _ ht i
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,Bos.upS,PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,map_add,price0,hr0,add_zero,map_zero] -- unknown

lemma core_price_at (hn:Admissible n) (i:ℕ): pull L ((1/2:ℂ) • docket n (Wilsonian.core G i)) =
    mask (i+2:ℤ) (-𝒥 LAND + ghostAction A b) + mask (i:ℤ) (𝒥 hrLog):= by
  unfold Wilsonian.core; change pull L ((1/2:ℂ) • (docket n ((model ((i:ℤ)+2) (Wilsonian.W G)) +(model ((i:ℤ)+0) (Wilsonian.H G))))) = _; rw [map_add,smul_add,map_add]; -- `duty` mask rule
  have he {t:ℤ}(F:Dot G Cover): pull L ((1/2:ℂ) • docket n (model t F))=mask t (pull L ((1/2:ℂ) • docket n F)):= by rw [show docket n (model t F)=_ from enterShim (b:=true) n t,← map_smul (mask t),pull_mask]; rfl
  rw [he,on_W,he,on_H _ _ hn]; simp only [add_zero]; rfl

lemma installedE (hn:Admissible n) : pullSeries L (posEnergy (Wilsonian.core G) n true) = f! (fixedAct A b) := by
  funext i; change pull L (posEnergy _ _ _ _) = _
  unfold posEnergy; split
  next h=> rw [Com.forget_at,h,PowerSeries.coeff_zero_eq_constantCoeff,fixed0,map_zero]; rfl
  next h=>
    rw [show pay true=(1/2:ℂ) from (by simp [pay]), core_price_at _ _ hn, Com.forget_at,fixedAct, map_add (ℳ i)]; unfold Glue.debit
    simp only [map_sum,Matrix.of_apply, Glue.Ω, PowerSeries.coeff_C_mul,Com.mul_val,Submodule.coe_add,Submodule.coe_sum, Matrix.map_apply,Bos.upS,PowerSeries.coeff_map,map_add, priceMat,PowerSeries.coeff_mk,hrMat, Bos.seriesInk,radiant,Matrix.sub_apply, Matrix.one_apply ]; -- inspect
    have hf(j k:κ): PowerSeries.coeff i (if j=k then (1:𝑩) else 0)=0:= by split <;> simp [PowerSeries.coeff_one,h]
    rw [ghost_mask]; simp only [FPInk, map_sub,hf,if_neg h, map_neg,sub_zero, Submodule.coe_neg,Bos.seriesInk, PowerSeries.coeff_mk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,bob_inside, Nat.cast_add,Nat.cast_ofNat]; abel
end YM.FVAAlt2
