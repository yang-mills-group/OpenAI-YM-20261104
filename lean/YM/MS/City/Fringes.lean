import YangMills.WilsonProof.NativeSupport.YM.MS.City.Lines
/-!
# Reciprocal translation with half-period signs

Use consistently on vector and antifield. Includes mixed line, Lap. Lower mark
 phases not weighted by physical test positions. Need at all lifted momenta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}
abbrev ticket (i: Atom Axis)(z:Cover):ℂ:= bill (rep z) (offset i)
variable (x:Cover)
lemma testv (i:Axis)(b:Bool): ticket (some i,b) x*ticket (some i,b) x=1:= by
   unfold ticket offset; dsimp only; rw [← rightadd (rep x), show ((1/2:ℝ) • embed (step i) +(1/2:ℝ) • embed (step i))= embed (step i) from (centr i).symm, reciprocal]
lemma testA (i:Atom Axis): ticket i x * ticket i x=1:= by rcases i with ⟨_|i,b⟩ <;> first | exact testv x i b| simp [ticket]
lemma rebate (i: Branch G Axis): veil x i=ticket i.1 x:= rfl
lemma testX (i:Branch G Axis): veil x i*veil x i=1:= testA x i.1
lemma backv (i:Branch G Axis): veil (-x) i=veil x i:= by rw [veil,map_neg,Tone.opp]; exact inv_eq_of_mul_eq_one_right (testA ..) -- maybe defeq
lemma stamp_neg (i:Atom Axis) : ticket i (-x)=ticket i x:= by rw [ticket,map_neg,Tone.opp]; exact inv_eq_of_mul_eq_one_right (testA ..)

variable (p:QP)
-- s_wave proof ratio using reciprocal directly.
lemma stampV (i:Axis)(b:Bool): ↑(wave (p+rep x) i)=ticket (some i,b) x * (wave p i:ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    have hv : bill (rep x) (-z i)=bill (rep x) (z i):= by rw [inverse]; exact inv_eq_of_mul_eq_one_right (testv x i b)
    rw [mul_left_comm I,← s_wave p i,← s_wave,payadd,payadd,hv]; change _= bill (rep x) (z i) * _; ring -- unfold same
lemma sq_stamp : (wave (p+rep x)).sq=(wave p).sq:= by
    unfold Momentum.sq; refine Finset.sum_congr rfl (fun i _=>?_); apply Complex.ofReal_injective; push_cast; rw [stampV x p i true,mul_pow,show ticket (some i,true) x^2=1 from (pow_two ..).trans (testv ..),one_mul]
lemma P_stamp (i j:Axis): ↑(precision i j (wave (p+rep x)))= ticket (Landau.gauge i) x* ticket (Landau.gauge j) x * (precision i j (wave p):ℂ):= by
    unfold precision; rw [sq_stamp]; push_cast; simp_rw [stampV x p _ false]; unfold delta; split; swap; · push_cast; ring
    next h=> subst j; rw [testA,one_mul]; congr 1; rw [mul_mul_mul_comm,testA,one_mul]
variable {H:Landau.Detect.Law G}
def Perk (T:Legs (LightMode G QP)→ℂ): Prop:= ∀ l r i p q,T (l++(i,p+rep q)::r)= veil q i * T (l++(i,p)::r)
-- flow line tests

def Near (K:Flux (Branch G Axis) QP ℂ): Prop:= ∀ q i j p, K i j (p+rep q)= veil q i*veil q j* K i j p
lemma L_stamp (r:ℝ): Near (G:=G) (LegsK wave r):= by
   intro x i j p; unfold LegsK Landau.choir; split; swap; · simp
   next h=>
      rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> first| (solve| simp [L0])| (simp only [L0,brush,sq_stamp]; push_cast; first| (simp_rw [P_stamp] ; rw [rebate,rebate]; ring)| (simp_rw [stampV x p _ true,rebate,ticket]; simp only [here_b,right0]; ring)) -- adjust
lemma part (x:Cover)(a:Axis)(i j:G.ColorIndex)(b c:Bool): veil x ((some a,b),i)* veil x ((some a,c),j)=1:=testv x a false
lemma X_stamp (r:ℝ): Near (G:=G) (LegsX wave r):= by
   intro x i j p; unfold LegsX Landau.choir; split; swap; · simp
   next h=>
       rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> first| (solve| simp [X0,laplace,veil]) | skip
       all_goals simp only [X0,laplace,delta,low,coat,scaling,sq_stamp]; first | (split_ifs <;> subst_vars <;> first | rw [part,one_mul] | simp )| simp [veil]
-- line Y or Q derivative later.
end YM.MS.City
