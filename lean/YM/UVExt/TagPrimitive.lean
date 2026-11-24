import YM.UVExt.ProfileRay

/-! Exact ray at a fixed real physical Gaussian displacement in one connected-activity construction. Keeping tags, charts and Coat, including Borel and support tests, fixed. Input noncoupling entries fixed on this ray. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.UVExt.EnergyRay
open RG Lattice Wilson Pressure Stores ConnectedActivityE6 Coat Raw Mask Pulse Itinerary
open scoped Topology BigOperators Classical

variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Tree.Forest S.ratio}
-- retain all BOOKKEEPING (path, clipping and activities); this is formal evaluation of the same rule with β multiplied by r, separately from whether the result is a lawful orbit.
def scaled (R:Rep G f) (r:ℝ) := { R with beta:=r*R.beta }
lemma scaled_one (R:Rep G f) : scaled R 1=R := by cases R; simp [scaled]

variable (X:Coat T F) (R:Rep G f) (a:ℝ) (z:Coat.Air f G) (Ñ:Precision.ChartRatio G) (r:ℝ)
    {W:ℝ} {l : Finset ℕ} {q:ℕ} (hr:0<r) (hβ:0<R.beta)

include hr hβ
lemma atmosphere_scaled : X.atmos (Real.sqrt r • z)=Real.sqrt r • X.atmos z := by
 ext i; rw [atmos,atmos]
 simp only [erect,Pi.smul_apply,PiLp.smul_apply,smul_eq_mul]
lemma same_link : X.liftA (scaled R r).beta (Real.sqrt r • z) = X.liftA R.beta z := by
 unfold liftA; rw [atmosphere_scaled _ _ _ _ hr hβ,smul_smul]; congr 2
 change _*(Real.sqrt r)=_; rw [show (scaled R r).beta=R.beta*r from mul_comm _ _]; exact Primitive.gstep_mul R.beta r hβ hr
lemma same_aperture (i) : X.aperture (scaled R r).beta (Real.sqrt r • z) a i = X.aperture R.beta z a i := by
 unfold aperture; rw [same_link _ _ _ _ hr hβ]

lemma hat_scaled : X.hatted (scaled R r).beta = Real.sqrt r • X.hatted R.beta := by
 unfold hatted gStep; rw [smul_smul]; congr 1
 dsimp only [scaled]
 rw [inv_inv, inv_inv,Real.sqrt_mul hr.le]; ring
lemma qlinear_scaled (i) : X.qlinear (scaled R r).beta (Real.sqrt r • z) i = r * X.qlinear R.beta z i := by
  rw [qlinear,qlinear, Finset.mul_sum,hat_scaled _ _ _ hr hβ]; apply Finset.sum_congr rfl; intro j _
  simp only [Pi.smul_apply,PiLp.smul_apply,smul_eq_mul]
  have := Real.sq_sqrt hr.le; linear_combination (z.ofLp (i,j)*X.hatted R.beta (i,j))*this

lemma qfirst_scaled (i) : X.qfirst (scaled R r).beta (Real.sqrt r • z) a i = r * X.qfirst R.beta z a i := by
 rw [qfirst,qfirst,same_aperture _ _ _ _ _ hr hβ,qlinear_scaled _ _ _ _ hr hβ]
 ring

lemma circle_scaled {n:ℕ} (i : Bond f) (p : Pulse.Itinerary f (n+2)) : X.circle (Real.sqrt r • z) i p = r * X.circle z i p := by
 dsimp only [circle]; simp_rw [PiLp.smul_apply, smul_eq_mul,← mul_assoc r,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
 apply Finset.sum_congr rfl; intro k _
 have := Real.sq_sqrt hr.le; linear_combination ((1/2)*(z.ofLp (i,j) * combo i p (X.finale n) j k * z.ofLp (arrive i p,k)))*this

lemma chain_scaled (p) : X.chain (scaled R r).beta (Real.sqrt r • z) a p = r * X.chain R.beta z a p := by
 unfold chain qunique; rw [same_aperture _ _ _ _ _ hr hβ, same_aperture _ _ _ _ _ hr hβ, circle_scaled _ _ _ _ hr hβ]; ring

lemma detect_scaled (p) : X.detect (X.liftA (scaled R r).beta (Real.sqrt r • z)) W a (scaled R r) l p = X.detect (X.liftA R.beta z) W a R l p := by rw [same_link _ _ _ _ hr hβ]; rfl

def isHotTag {c f:Side} (p : Coat.LogIndex c f) :=
  match p with
  | .inl (.inl _) => false
  | .inl (.inr (.inl _)) => true -- cubic
  | .inl (.inr (.inr (.inl _))) => true -- quartic
  | .inl (.inr (.inr (.inr (.inl _)))) => false -- loop
  | .inl (.inr (.inr (.inr (.inr _)))) => true -- pairs
  | .inr (.inl (.inl _)) => true -- speck
  | .inr (.inl (.inr _)) => false
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr (.inl _))) => false
  | .inr (.inr (.inr (.inr (.inl _)))) => false
  | .inr (.inr (.inr (.inr (.inr _)))) => true

lemma expo_scaled (p:Raw.LogLetter c f) (U) : Raw.expo T X.x (scaled R r) U X.V p = (if isHotTag (.inl p) then r else 1)* Raw.expo T X.x R U X.V p := by
  dsimp [expo]
  rcases p with s|t|u|v|w|x <;> simp only [isHotTag,Sum.elim,translateValue,pairValue,scaled,Bool.false_eq_true,↓reduceIte,one_mul] <;> try ring
lemma short_scaled (p : Coat.Miniature c f) (u) : X.Short u Ñ (scaled R r).beta a p = (if isHotTag (c:=c) (f:=f) (.inr (.inl p)) then r else 1)*X.Short u Ñ R.beta a p := by
 rcases p with s|t
 · dsimp only [Short,Sum.elim,speck]; split
   · simp
   change -(r*R.beta)*_*_=r*_
   ring
 · simp only [isHotTag, Short, Sum.elim, ↓reduceIte, Bool.false_eq_true, one_mul]
lemma fuel_scaled (p : Coat.ChainIndex f) : X.fuel a (scaled R r).beta (Real.sqrt r • z) p = (if isHotTag (c:=c) (.inr (.inr p)) then r else 1)*X.fuel a R.beta z p := by
 rcases p with i|i|i|i|i <;> simp only [Coat.fuel,isHotTag,↓reduceIte,Sum.elim,Bool.false_eq_true,one_mul]
 all_goals first | rfl | exact qfirst_scaled _ _ _ _ _ hr hβ _ | exact chain_scaled _ _ _ _ _ hr hβ _
lemma farLog_scaled (p : Coat.LogIndex c f) : X.farLog (scaled R r) a Ñ (Real.sqrt r • z) p = (if isHotTag p then r else 1)*X.farLog R a Ñ z p := by
 dsimp only [farLog]; rw [same_link _ _ _ _ hr hβ]
 rcases p with p|p|p
 · dsimp only [Sum.elim,inhale]; rw [expo_scaled _ _ _ hr hβ p,show Raw.space _ _ _ (scaled R r) p= Raw.space T _ X.B R p from rfl]; ring
 · exact short_scaled _ _ _ _ _ hr hβ _ _
 · exact fuel_scaled _ _ _ _ _ hr hβ _

lemma bag_scaled (p) : X.bag (scaled R r) a (X.liftA (scaled R r).beta (Real.sqrt r • z)) p = X.bag R a (X.liftA R.beta z) p := by rw [same_link _ _ _ _ hr hβ]; rfl

def seedPower (A : Stores S) : ℕ := (X.pens A).card*Fintype.card G.ColorIndex
def seedBill (A : Stores S) (u) := -(R.beta*(X.quoteNear A u+X.far_bills A))

lemma measure_scaled : Coat.measure_g Ñ (scaled R r).beta = Coat.measure_g Ñ R.beta /(Real.sqrt r)^Fintype.card G.ColorIndex := by
 have he : Coat.gStep (scaled R r).beta= Coat.gStep R.beta / Real.sqrt r := (eq_div_iff (Real.sqrt_pos.mpr hr).ne').2 (by change gStep (r*R.beta)*_= _; rw [mul_comm r]; exact Primitive.gstep_mul R.beta r hβ hr)
 rw [measure_g, measure_g, he, ←mul_div_assoc, div_pow]; rw [mul_div_assoc]

variable (hÑ : Ñ.scale ≠ 0)
include hÑ
lemma steamLog_scaled (A : Stores S) (u) : X.steamLog (scaled R r) Ñ a A u=(r-1)*seedBill X R A u+X.steamLog R Ñ a A u + seedPower X A * Real.log (Real.sqrt r) := by
 have hp := Real.sqrt_pos.mpr hr
 have he : Real.log (Coat.measure_g Ñ (scaled R r).beta)=Real.log (Coat.measure_g Ñ R.beta)-Fintype.card G.ColorIndex*Real.log (Real.sqrt r) := by
   -- even Ñ scale nonpositive? for zero log 0; need positivity Ñ
   rw [measure_scaled R Ñ r hr hβ,Real.log_div (show Coat.measure_g Ñ R.beta ≠0 from mul_ne_zero hÑ (pow_ne_zero _ (by have := Real.pi_pos; unfold gStep; positivity))) (pow_ne_zero _ hp.ne'),Real.log_pow]
 dsimp only [steamLog]; rw [he]; unfold seedBill scaled seedPower; push_cast; ring

lemma pack_scaled (A : Stores S) (u) : X.Pack (scaled R r) Ñ l W a A u=Real.exp ((r-1)*seedBill X R A u) * (Real.sqrt r)^seedPower X A * X.Pack R Ñ l W a A u := by
 dsimp only [Pack]; split
 · unfold steam; simp only [steamLog_scaled X R a Ñ r hr hβ hÑ A, Real.exp_add,Real.exp_nat_mul,Real.exp_log (Real.sqrt_pos.mpr hr)]
   simp only [Contract.order,Contract.charges,Contract.covered,scaled]; ring
 simp

open Primitive
def takeBill (A : Stores S) := seedBill X R A (X.liftA R.beta z)

def capsule (p:Head S) : Primitive :=
 match p with
 | .inl A => .thermal ((X.vertex R Ñ W a l q z p * Real.exp (-takeBill X R z A) : ℝ):ℂ) (takeBill X R z A) (seedPower X A)
 | .inr (.inl _) => .thermal (X.vertex R Ñ W a l q z p:ℝ) 0 0
 | .inr (.inr (.inl i)) => if isHotTag i then .split (X.farLog R a Ñ z i) else .thermal (X.vertex R Ñ W a l q z p:ℝ) 0 0
 | .inr (.inr (.inr _)) => .thermal (X.vertex R Ñ W a l q z p:ℝ) 0 0

lemma restores (p:Head S) : (capsule X R a z Ñ (W:=W) (l:=l) (q:=q) p).run r = (X.vertex (scaled R r) Ñ W a l q (Real.sqrt r • z) p:ℝ) := by
 rcases p with p|p|p|p
 · dsimp only [capsule]; rw [standard _ _ _ _ hr]
   simp only [vertex,Sum.elim]; split
   · rw [same_link _ _ _ _ hr hβ,pack_scaled _ _ _ _ _ hr hβ hÑ]
     unfold takeBill; rw [show (r-1)*seedBill _ _ _ _ = r*seedBill X R p (X.liftA R.beta z)+ -seedBill _ _ _ _ by ring,Real.exp_add]
     push_cast; ring
   simp
 · rw [capsule,basic]; dsimp only [vertex,Sum.elim]; rw [bag_scaled _ _ _ _ _ hr hβ]
 · dsimp only [capsule,vertex,Sum.elim]; unfold raiseAir; rw [farLog_scaled _ _ _ _ _ _ hr hβ, Complex.ofReal_sub,Complex.ofReal_one]; split
   · dsimp only [run]; push_cast; rfl
   rw [basic,one_mul]
   push_cast; rfl
 rw [capsule,basic]; dsimp only [vertex,Sum.elim]; rw [detect_scaled _ _ _ _ _ hr hβ]

end YM.UVExt.EnergyRay
