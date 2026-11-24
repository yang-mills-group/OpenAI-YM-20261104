import YM.FVA2.Lambda.Pure
/-!
# Detect the matched log slope on the same Team series relative to TaylorOK

 Upper n parity. Producing identities of differences between native $y$ at finite
 log(UV), through cubic. Needed for extracting the measured beta. Include both ghost
 and axis slots. Auxiliary no derivative-of-limit.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Finite
open Function Filter Set Finset MeasureTheory Real Metric
open Lattice MS MS.Plane MS.Plane.Wire MS.Momentum MS.Koszul MS.Native MS.Landau MS.Tone MS.Tone.Frame MS.Native.Wilsonian MS.Book MS.Book.Convolve MS.Book.Program
open MS.City MS.Heat MS.Heat.Signal MS.Wind MS.Menus MS.Landau.Detect MS.Landau.Detect.Mark MS.Cylinder MS.Cylinder.Lab
open MS.High MS.High.Knobs
open PowerSeries (coeff coeff_mk)
open Hue.Agent Hue.Agent.Kappa
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:ℕ} {p:Team} (hp: Kappa.Correct p)
section scope
-- take q=p with wave two set zero; also no coupling two by hp. Then style unaffected at n≤2.
variable {q:Team} {u:ℕ} (hx:∀ i, 0 < i→i ≤ u → (q i).waveA=0 ∧ (q i).waveC=0 ∧ (1 < i→(q i).coupling=0))
include hx
lemma sameHome (x y:ℝ)(n:ℕ)(h:n≤u): style G q x n= style G q y n:= by
  have hP: Rem (shift q x) (shift q y) n:= by intro i hi; unfold shift; rw [coeff_mk,coeff_mk]; split_ifs with ht hv; rfl; rfl; simp [ (hx i (by omega) (hi.trans h)).2.2 (by omega) ]
  have hr (Z: ℕ→ Polynomial ℝ)(hZ:∀ i,0 < i→ i≤ n → Z i=0): Rem (affirmative Z x) (affirmative Z y) n:= by
    intro i hi; by_cases ht:i=0; · simp [ht,affirmative]
    simp [ affirmative, ht, hZ i (Nat.pos_of_ne_zero ht) hi ]
  have he (i:Atom Axis): Rem (adap q i x) (adap q i y) n:= by
     obtain ha:= hr (fun i=> (q i).waveA ) (fun i p q=>(hx i p (q.trans h)).1); obtain hb:= hr (fun i=> (q i).waveC ) (fun i p q=> (hx i p (q.trans h)).2.1); cases i with| mk i j =>cases i <;> cases j <;> first| assumption| exact ha| exact hb | exact tickets ha | exact tickets hb
  unfold style wobble; rw [ LinearMap.comp_apply,LinearMap.comp_apply,rolls,rolls ]; refine Finset.sum_congr rfl fun i hi => ?_; obtain hv:= mem_antidiagonal.mp hi
  rw [ sub_alt (fun j hj=> hP j (hj.trans (by omega)) : Rem _ _ i.2 ) ]; apply Subtype.ext; ext l; rw [train_v,train_v,offer,offer,compositeList (V:=Y q x) (W:= Y q y) (fun i=> he i.1.1) l i.1 (by omega)]
variable {Q:Dec G}(h:PC G q Q)
include h
lemma before (x y:ℝ) (n:ℕ)(hi:n ≤ u) : Q n x= Q n y:= by
 induction n using Nat.strong_induction_on with
 | _ n ih=>
     by_cases h0:n=0; · rw [h0,h.free]; rfl
     obtain hp:=h.recu _ (Nat.pos_of_ne_zero h0) x; obtain ht:=h.recu _ (Nat.pos_of_ne_zero h0) y
     have hv: (Wind.path (1/2) n 1 Q Q) x=( Wind.path (1/2) n 1 Q Q ) y:= by unfold Wind.path; rw [ Pi.smul_apply,Pi.smul_apply, Finset.sum_apply,Finset.sum_apply]; congr 1; apply Finset.sum_congr rfl; intro i hi'; obtain ha:=path_in hi'; rw [ih _ (by omega : n-i<n) (by omega), ih _ ha.2 (by omega) ]
     rw [hv, sameHome hx x y n hi] at hp; have He:= Touch_near (( h.owes n ).stay x) (( h.owes n ).stay y) hp ht (ranked h n x) (ranked h n y)
     apply sub_eq_zero.mp; apply Dtotal He; rw [ Pi.sub_apply,hp.1, ht.1, sub_self ]
end scope
-- price wave orientation: ranktwo minus in choosing q upward.
set_option quotPrecheck false
local notation "αs" => -(p 2).waveA
local notation "Λ" => -(p 2).waveC
local notation "q" => rush p αs Λ 2
include hp
private lemma takes (i:ℕ)(hi:0 < i)(hv:i≤2): ((q) i).waveA=0 ∧ ((q) i).waveC=0 ∧ (1 < i→ ((q) i).coupling=0):= by
 interval_cases i
 · simp [rush,(hp.tone 1).a (by decide),(hp.tone 1).c (by decide)];
 simp [rush,(hp.tone 2).g (by decide) (by decide)]
lemma second (x t:ℝ)(w:List (Lane4 G))(hw: Course true w)(ht:w.length=2)(hx:fieldDim wfield w+n≤4): torch n ( skyline G p 2 x t ) w- torch n ( skyline G q 2 0 t ) w= if fieldDim wfield w+n=4 then ranktwo (2*((αs).eval x)) ((Λ).eval x-(αs).eval x) w else 0:= by
  let X:=skyline G p; let Y:=skyline G (q); rw [ ← torch_sub (M:= skyline G p 2 x t ) (W:= skyline G (q) 2 0 t ) w ( (( skyPC G p ).owes 2).stay x|>.joint.routine (ray w) t ) ( (( skyPC G (q) ).owes 2).stay 0|>.joint.routine (ray w) t ), ← before (takes hp) (skyPC G (q)) x 0 2 (by decide) ]; exact ( bulk_pay ( skyPC G p ) ( skyPC G (q) ) ( scale_car p (-(p 2).waveA) (-(p 2).waveC) (k:=2) (by decide) ) (by decide)|>.pay x t w hw ht n hx ) -- parentheses
omit hp in
lemma identical_loop (h:PC G p (skyline G p))(x y t:ℝ)(w:List (Lane4 G))(hw:w.length=n): Wiref G (skyline G p n x) t w= Wiref G (skyline G p n y) t w:= by
   let g(s:ℝ):= skyline G p n s; have hu (i:ℝ): Wiref G (g i) t= Ccy (Cpu G t) (g i t) μzone:= finite_cc μzone (period0 μzone cour0 (main_f _) (((h.owes n).stay i).joint)); rw [ ← show g x=skyline G p n x from rfl, ← show g y=skyline G p n y from rfl, hu,hu ]; unfold Ccy; congr! 1; funext p'; change Flux.trc _ _ _ w= _; simp_rw [ Flux.at_trc]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> congr_arg (Cpu G t i j p'*·) (highest h x y t _ (by simp only [List.length_cons,hw] )) -- unfolds g? fix
lemma tip (i j k:G.ColorIndex) (x:ℝ): token (Tone.run ( style G p x 3 )) i j k = ↑((p 3).coupling.eval x+(p 2).waveC.eval x) * (LieColor i j k:ℂ) + token (Tone.run ( core G 3 )) i j k:= by
  let χ:= [Detect.S i 0, C j 0, C k 0]; let T(a:ℕ):= run (core G a); let W:=adap p ghost x; let A (a:ℕ):= substitute (shift p x) (core G) a; let α:= (↑((p 3).coupling.eval x):ℂ); let β:= (↑((p 2).waveC.eval x):ℂ)
  have he: (χ.map (fieldV p x ∘ Prod.fst)).prod=W := by
     have he: W * (adap p gaugeC x)= (1:Cn):= by exact Program.pairs (fun i=> (p i).waveC) x
     change _= W; unfold χ; change (adap p gaugeC x)*(W*(W*1))=_; rw [mul_one,← mul_assoc,mul_comm (adap p gaugeC x) _, he,one_mul]
  have hf: coeff 2 W= β:= (by simp [W,adap,affirmative,β]); have hg: coeff 1 W=0:= v_b x ( show Wage 1 p from fun i _=> hp.tone i ) _ 1 le_rfl (by decide); have ht: T 0 χ=0:= Tone.oneRank (participates G 0) χ (by simp [χ]); have hQ: Program.cut (shift p x) 1 3=α:= by simp [Program.cut,shift,α];
  have hb: Program.cut (shift p x) 3 3=1:= by exact ( Reg.Token.stamp_n ( shift p x ) (share ..) 3 ).trans (by rw [ann,one_pow]);
  have ha: T 1 χ= ( LieColor i j k:ℂ ) := by
     have hp : T 1 χ= Menus.Top G χ:=( enough _ (by simp [χ]) ).symm; refine hp.trans (Eq.trans ?_ (token_R i j k)); rw [ show token _ i j k= torch 0 (Menus.Top G) χ from skin_eq _ _ _ ( by rfl ) ]; simp [torch_at,reading,χ] -- maybe rfl
  have hP: run (A 3) χ=α*( LieColor i j k:ℂ )+T 3 χ:= by
     unfold A; rw [ rules,map_sum, Finset.sum_apply ]; simp_rw [ map_smul,Pi.smul_apply,smul_eq_mul ]; rw [ ← Nat.range_succ_eq_Iic ]; simp only [Finset.sum_range_succ,Finset.sum_range_zero,hQ,hb, show Program.cut (shift p x) 0 3=0 by simp [Program.cut], show Program.cut (shift p x) 2 3=0 from Hue.Agent.powers (shift_b x ( show Wage 3 p from fun i _=> hp.tone i )) 2 3 le_rfl (by decide), zero_mul,one_mul,zero_add,add_zero ]; rw [ ← ha ]
  unfold style token; rw [wobble, LinearMap.comp_apply,rolls,map_sum,Finset.sum_apply ]; change ∑ v'∈ antidiagonal (3:ℕ), run (train (Y p x) v'.1 (A v'.2)) χ = _; simp_rw [funds, he]; rw[ Finset.Nat.sum_antidiagonal_eq_sum_range_succ ( f:=fun i j=> coeff i W * run (A j) χ ) ]; simp only[Finset.sum_range_succ,Finset.sum_range_zero,zero_add]; norm_num only; rw [ show coeff 0 W=1 from adap0 p x _,hg,hf,hP, show run (A 0) χ=0 from (by unfold A; rw [Program.pay0]; exact ht), show A 1=core G 1 from sub_one p x (core G), show run (core G 1) χ= (LieColor i j k:ℂ) from ha ]; change _=( _+_:ℝ ) * (LieColor i j k:ℂ) + T 3 χ; push_cast; unfold α β; ring
lemma third (i j k:G.ColorIndex)(x t:ℝ): Mark.token (skyline G p 3 x t) i j k-Mark.token (skyline G p 3 0 t) i j k= ((( p 3 ).coupling.eval x+(p 2).waveC.eval x)-( (p 3).coupling.eval 0+(p 2).waveC.eval 0 ):ℝ ) * (LieColor i j k:ℂ) := by
  let χ:= [Detect.S i 0,C j 0,C k 0]; let X:= skyline G p; have he:= skyPC G p; let A(t:ℝ):= X 3 x t χ-X 3 0 t χ; have hA(t:ℝ): HasDerivAt A 0 t:= by
      have hh (x y:ℝ): Wind.path (1/2) 3 1 X X y x χ=0:= by
          unfold Wind.path; simp only [ Pi.smul_apply, Finset.sum_apply ]; apply Eq.trans ?_ (smul_zero (1/2:ℝ)); congr 1; refine Finset.sum_eq_zero (fun i _=>?_); change Flux.tree _ (Cpu G x) _ _ _=0; simp [Flux.tree,χ, Flux.attaches,scatter_cons,scatter_nil,net,Detect.S,C,qnote,SpaceOut.coach_zero]
      convert! ((he.recu 3 (by decide) x).2 t χ).sub ((he.recu 3 (by decide) 0).2 t χ) using 1; rw [Pi.add_apply,Pi.add_apply, identical_loop (n:=3) he x 0 t χ rfl, show Wind.path (1/2) 3 1 (skyline G p) _ x t χ=0 from hh t x, show Wind.path (1/2) 3 1 (skyline G p) _ 0 t χ=0 from hh t 0,sub_self ]
  change A t =_; rw [ Wind.constancy hA t ]; unfold A; simp_rw [X,(he.recu 3 (by decide) _).1 ]; change token _ _ _ _ - token _ _ _ _ = _; rw [tip hp i j k, tip hp i j k, Complex.ofReal_sub ]; ring
end YM.FVA2.Lambda.Finite
