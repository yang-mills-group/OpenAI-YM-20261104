import YM.FVA2.Rank.Mon
/-! # Reflected parity for bulk lattice teams. Work to fixed degree k. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hue.Agent
open Function Filter Set Finset Lattice MeasureTheory
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Native MS.Native.Wilsonian MS.Book MS.Book.Program MS.Book.Convolve
open MS.Tone MS.High MS.Menus MS.Color MS.Cylinder
open Complex (I)
open PowerSeries (coeff)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{k i j m:ℕ}{p:Team}
-- at order n. No restriction on unused slots (n=0 for both, n=1 coupling). Coupling and field waves are real polynomials.
structure Spare (n:ℕ)(p:Plan) : Prop where
 a : n%2≠0 → p.waveA=0
 c : n%2≠0 → p.waveC=0
 g : n>0 → n%2=0 → p.coupling=0
abbrev Wage (k:ℕ)(p:Team):= ∀ i≤k, Spare i (p i)
-- homogeneous series through k
variable (y:ℝ) {f g:Cn} (h: Wage k p)
def Bill (k i:ℕ)(f:Cn):=∀ j,j≤k→ j%2≠i%2→coeff j f=0
lemma b_mul (h:Bill k i f)(ha:Bill k j g): Bill k (i+j) (f*g):= by
    intro a H h'; rw [PowerSeries.coeff_mul]; refine Finset.sum_eq_zero (fun c hc=>?_); obtain hm:= Finset.mem_antidiagonal.mp hc; by_cases hv: c.1%2=i%2; · rw [ha c.2 (by omega) (by omega),mul_zero]
    rw [h _ (by omega) hv,zero_mul]
lemma constant (k:ℕ):Bill k 0 1:= by intro j a h; rw [ PowerSeries.coeff_one ]; split <;> first|rfl|omega
lemma powers {g:Cn}(h:Bill k 1 g)(j:ℕ): Bill k j (g^j):= by
    induction j with| zero=> rw [pow_zero]; exact constant k| succ i ih=> rw [pow_succ]; exact b_mul ih h
lemma bInv (h:Bill k 0 f): Bill k 0 (PowerSeries.invOfUnit f 1):= by
    intro i; induction i using Nat.strong_induction_on with
    | h i ih =>
        intro hi he; rw [PowerSeries.coeff_invOfUnit]; split; next h=> omega
        next H =>
         rw [ Finset.sum_eq_zero (fun j hj=>?_),mul_zero]; obtain ht:=mem_antidiagonal.mp hj; split; next th=>
            by_cases ht':j.1%2=0; · rw [ih j.2 th (by omega) (by omega),mul_zero]
            rw [ h _ (by omega) ht',zero_mul]
         next H'=> rfl
include h
lemma shift_b : Bill k 1 (shift p y):= by
    intro j hj hc; have hl:= h j hj; unfold shift; rw [PowerSeries.coeff_mk]; split_ifs with he ht; rfl; exfalso; omega; rw [ hl.g (by omega) (by omega), Polynomial.eval_zero,Complex.ofReal_zero ]
lemma v_b (t:Atom Axis):Bill k 0 (adap p t y):= by
    have he (Q:ℕ→Polynomial ℝ)(hp:∀ i≤k,i%2≠0→Q i=0): Bill k 0 (affirmative Q y):=by
       intro j hj ht; simp only [affirmative,PowerSeries.coeff_mk, if_neg (show ¬ j=0 from (by omega)),hp j hj (by omega),Polynomial.eval_zero,Complex.ofReal_zero]
    unfold adap; have ha:= he (fun i=> (p i).waveA) fun i hi=> (h i hi).a; have hb:= he (fun i=> (p i).waveC) fun i hi=> (h i hi).c; rcases t with ⟨_|t,_|_⟩ <;> first|assumption|exact bInv ha| exact bInv hb
lemma v_l (l: List (LightMode G Cover)): Bill k 0 ( l.map ( Y p y ) ).prod:= by
    induction l with| nil=>exact constant k| cons i l ih=> rw [List.map_cons,List.prod_cons]; exact b_mul (v_b y h i.1.1) ih
omit h
lemma location (n:ℕ)(G:Gauge): Hue.only n (core G n).val:= by
    intro i hi; change (( mask ((n:ℤ)+2) (W G).val) i +(mask (( n:ℤ )+0) (H G).val) i)= _; rw [ strange _ ( by omega ), strange _ ( by omega ),add_zero ]
lemma toneH (F:Dot G Cover) (h:Hue.only i F.val): Hue.only i (run F):= by
    intro l hl; rw [← enough l (F:=run F) (show ( l.length:ℤ )=l.length from rfl),← Tone.grade ]; have ht : model (l.length:ℤ) F=0:= by apply Subtype.ext; ext w; by_cases he:w.length=l.length; exact (enough w (by exact_mod_cast he: ( w.length:ℤ )=l.length)).trans (h w (by omega)); exact strange _ (show (w.length:ℤ)≠ l.length from by omega)
    rw [ht,map_zero]; rfl
include h
lemma substitute_alt {X:ℕ→ Dot G Cover}(hb:∀ i≤k,Hue.only (m+i) (X i).val)(j:ℕ) (hJ:j≤k): Hue.only (m+j) ( substitute (shift p y) X j ).val:= by
    intro l he; simp only [rules,sum_stack,Finset.sum_apply,Submodule.coe_smul, Pi.smul_apply]; refine Finset.sum_eq_zero (fun i hi=>?_); by_cases hh: j%2=i%2; · rw [hb i (le_trans (Finset.mem_Iic.mp hi) hJ) l (by omega),smul_zero]
    unfold Program.cut; rw [powers (shift_b y h) i j hJ hh,zero_smul]
lemma bill_p {X:ℕ→ Dot G Cover}(hb:∀ i≤k,Hue.only (m+i) (X i).val) (j:ℕ) (hj:j≤k): Hue.only (m+j) (wobble G p y X j).val:= by
 intro l h'; unfold wobble; rw [LinearMap.comp_apply, rolls, sum_stack, Finset.sum_apply]; refine Finset.sum_eq_zero (fun i hi=>?_); obtain HE:=mem_antidiagonal.mp hi; rw [train_v, offer]; by_cases h1:i.1%2=0; · rw [ substitute_alt y h hb i.2 (by omega) l (by omega), mul_zero ]
 rw [ v_l y h l i.1 (by omega) h1,zero_mul ]
theorem first_p (i:ℕ) (hi:i≤k) (G:Gauge): Hue.only i (run (style G p y i)):= toneH _ (by simpa only [zero_add,style] using bill_p (m:=0) y h (fun j _=> by rw [ zero_add ]; exact location j G ) i hi)
end YM.FVA2.Hue.Agent
