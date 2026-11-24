import YM.MSbar.Grass.Vector

/-! `[Q0,∂²]` gives the IR kernel in the effective master identity. Compute purely finite algebra
first, with finite support only required on the Lap/lines (not on the entire symbol).
Includes exact performance statement whose formulas via LinearMap sum can apply after large index.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset Finsupp
open scoped BigOperators Classical
variable {T:Type*} {p:T→Bit} {f g : Series T}{x y:T} {d e r k : Bit} {P D : Stock T}

-- linearization in stock index
abbrev lump (T:Type*) : Stock T →ₗ[ℂ] Order T:= Finsupp.linearCombination ℂ (fun x=> (2:ℂ)⁻¹ • twice x)
lemma lumps (P : Stock T): laps P=lump T P:=by
    unfold laps lump Finsupp.linearCombination; dsimp [Finsupp.sum]; simp_rw [smul_smul]; simp only [div_eq_mul_inv]
lemma laps_sum {ι:Type*} (X:Finset ι)(F:ι→Stock T): laps (∑ i∈X,F i)=∑ i∈X,laps (F i):=by simp_rw [lumps];exact map_sum ..
lemma laps_single (a:T × T)(c:ℂ): laps (Finsupp.single a c) f=(c/2) • field a.2 (field a.1 f):=by rw [lumps,Finsupp.linearCombination_single]; simp [div_eq_mul_inv,twice,smul_smul]
lemma lap_add : laps (P+D)=laps P + laps D:= by simp_rw [lumps,map_add]
lemma lap_smul (c:ℂ): laps (c • P)= c • laps P:= by simp_rw [lumps,map_smul]
lemma lap_neg : laps (-P) = -laps P:= by simp_rw [lumps,map_neg]

namespace Transport
variable (X:Transport p r)
def leftCarry (x:T×T) (c:ℂ): Stock T := ∑ v∈(X.coeff x.1).support,Finsupp.single (v,x.2) (c*X.coeff x.1 v)
def rightCarry (x:T×T) (c:ℂ): Stock T := ∑ v∈(X.coeff x.2).support,Finsupp.single (x.1,v) (sign r (p x.1)*c*X.coeff x.2 v)

def born (P:Stock T):Stock T:= -(∑ x∈P.support,(X.leftCarry x (P x)+X.rightCarry x (P x)))
lemma left_lap (x:T×T)(c:ℂ) : laps (X.leftCarry x c) f =(c/2) • field x.2 (X.row x.1 f):=by
   unfold leftCarry; rw [laps_sum,X.cost]; simp only [LinearMap.sum_apply,map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro b h; rw [laps_single,map_smul,smul_smul]; congr! 1; ring
lemma right_lap (x:T×T)(c:ℂ) : laps (X.rightCarry x c) f=(c/2) • sign r (p x.1) • X.row x.2 (field x.1 f):=by
   unfold rightCarry; rw [laps_sum,X.cost]; simp only [LinearMap.sum_apply,map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro b h; rw [laps_single]; simp_rw [smul_smul]; congr! 1; ring
lemma commute (hp:Grade p 0 P) : X.lift (laps P f)-laps P (X.lift f)=laps (X.born P) f:=by
    unfold born;rw [lap_neg,laps_sum,LinearMap.neg_apply,LinearMap.sum_apply]; rw [price_loop, price_loop,map_sum]; rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl
    intro x hx; have he: sign r (p x.1)*sign r (p x.2)=1:=by rw [← sign_add_right,hp _ hx,sign_zero]
    rw [map_smul,X.leg,map_add,map_smul,X.leg,lap_add,LinearMap.add_apply,left_lap,right_lap]
    -- no Sym required
    simp only [smul_add,smul_smul,←mul_assoc]; funext v; simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]; linear_combination -(P x/2*X.lift (field x.2 (field x.1 f)) v)*he

local notation "b" => pairs p 0 P
local notation "d'" => pairs p 0 D
local notation "A" => laps P
local notation "C" => X.lift
lemma rates (hp: Grade p 0 P)(hD: Grade p r D)(he:D=X.born P)(hf:Homogeneous p 0 f):
    C (b f f)= d' f f+(2:ℂ) • b f (C f):=by
    have hC (f:Series T): C (A f)=laps D f+A (C f):= sub_eq_iff_eq_add.mp (by rw [he]; exact X.commute hp)
    have hv:= hC (join p f f); let g:=laps P f; have hg:Homogeneous p 0 (A f):= by simpa using hp.homogeneous hf
    simp only [hp.double hf,hD.double hf,X.derivation hf hf,hf.cm (X.manages hf),sign_zero,one_smul,map_add,map_smul,X.derivation hf hg] at hv
    rw [hg.cm (X.manages hf),hC,hp.first hf] at hv
    -- simplify individually
    funext w; replace hv:=congr_fun hv w; simp only [join_add_right,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at *; linear_combination hv
end Transport
end YM.MSbar.Super
