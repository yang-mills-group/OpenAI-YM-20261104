import YM.AllOrder.Plateau.Sail
import YM.AllOrder.Haiku.Tornado
import YM.AllOrder.Haiku.Route
import YM.AllOrder.Local.Carbon
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll
open ConnectedActivityE6.Coat
open AbsoluteSums Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n : Side} {k j w N : ℕ}
variable (A:ℕ→Atom G k) {σ C Z D β x:ℝ}
local notation "E"=>Positions (Primary n G)
local notation "L"=>Kinetic.Port.exteriorL G n
abbrev staff (p:Clip)(R:PathData G) (n:Side) := mainTerm p R ∘ represent ∘ tint G (Exterior.Body 1 n)
abbrev drift (p:Clip)(R:PathData G)(α:ℝ) (n:Side) :=draft (c:=n) α R p ∘ tint G (Exterior.Body 1 n)
local notation "S" => PhysicalNext.Repeat.Shellac.off
section off
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
@[simp] lemma off_ya (f g:X→Y) : S (f+g)=S f+ S g:=by ext1 x; change (f x+g x)-(f 0+g 0)= _+_; unfold Shellac.off; simp only [Pi.sub_apply]; abel
@[simp] lemma off_sc (f:X→Y)(β : ℝ) : S (β • f) = β • S f := by ext1 x; change β • f x- β • f 0= β •(f x-f 0); rw [smul_sub]
lemma taylor_off (f:X→Y)(k:ℕ)(h:ContDiffAt ℝ (↑k) f 0) : blockTaylor k (S f)= S (blockTaylor k f):= by
    ext1 x; unfold Shellac.off; simp only [Pi.sub_apply,blockTaylor_zero]; unfold blockTaylor Tensor.diagonal; rw [Finset.sum_apply,Finset.sum_apply,sum_range_succ',sum_range_succ']; simp_rw [Tensor.coeff_apply_zero]; let A:=fun (_:X) => f 0; rw [Pi.sub_apply, sub_self,add_zero, add_sub_cancel_right]; apply Finset.sum_congr rfl; intro i hi; have hh:= Finset.mem_range.mp hi; unfold Tensor.coeff; rw [iteratedFDeriv_sub_apply (h.of_le (show ((i+1:ℕ):WithTop ℕ∞)≤ ↑k from (by exact_mod_cast (show i+1≤ k from hh)))) contDiffAt_const, iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]
end off
section bare
variable (p:Clip)(R:PathData G)(α:ℝ)(hp:R.Bounds p σ C D) (hG:G.Simple)
local notation "X"=> staff p R n
local notation "Y"=> drift p R α n
include hp
lemma cursor (A:BareRates.pre G σ C k)(x:E)(hx:x∈ball 0 1) : ContDiffAt ℝ ω X x ∧ ContDiffAt ℝ ω Y x := let h:= bareSocket n A hp hx α; ⟨h.1,h.2.1⟩
lemma sector (x:E) : Stipend p R α k n ((L).symm x)=jet X (k+2) x+jet Y k x:= by
   let a:= staff p R n; let b:=drift p R α n; let f: Link G n→L[ℝ] E:= (L).toContinuousLinearMap; have h:ContDiffAt ℝ ω X 0∧ContDiffAt ℝ ω Y 0:=cursor p R α hp (Classical.choice (BareRates.offered _ _ _ 0)) _ (mem_ball_self zero_lt_one)
   change jet (X∘f) (k+2) _+ jet (Y ∘ f) k _=_; rw [Kinetic.pivot f _ _ h.1,Kinetic.pivot f _ _ h.2]; change _=_; simp only [f, ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] -- fix
include hG
lemma first_main (x:E): jet X 1 x=0:=by
 let f:= (L).toContinuousLinearMap; have h: (staff p R n) ∘ f = _ := (show (staff p R n) ∘ f= mainTerm p R ∘ Stationary.input G n from rfl)
 have ht: ContDiffAt ℝ ω X 0:=(cursor p R 0 hp (Classical.choice (BareRates.offered _ _ _ 0)) _ (mem_ball_self zero_lt_one)).1
 let W:= ((L).symm x); have hv:=Kinetic.pivot f X W ht 1; rw [show f W=x from (L).apply_symm_apply _,h] at hv; rw [←hv]; have H:= shore p R 0 hp n|>.1; unfold jet; rw [Project.still_one hG H.stained H.analytic]; simp
open Local.Pure
local notation "G₁"=>gStep β
local notation "Z"=> S (X)
lemma fixedS (x:E)(r:ℕ) (he:0<β) :  β*blockTaylor (r+2) X x + blockTaylor r Y x = β*(X 0)+ ∑ k∈ Finset.range (r+1), (gStep β)^k * Stipend p R α k n (bend (gStep β) x):= by
 let s:=gStep β; let z:=bend s x; let y:=L z; have hp'(f:E→ℝ)(k:ℕ) : blockTaylor k f x=∑ i∈ Finset.range (k+1),s^i*chip f i y:= by nth_rw 1 [←unbend s x (gS _ he|>.1)]; exact bill_insert ..
 rw [hp' X (r+2), hp',sum_range_succ' _ (r+2),sum_range_succ' _ (r+1)]; rw [show chip X 1 y=0 from first_main p R hp hG y,show chip X 0 y=_ from Tensor.coeff_apply_zero X 0 (fun _=> y)]; simp only [mul_zero, add_zero,pow_zero,one_mul,mul_add,Finset.mul_sum]; rw [add_comm _ (β*(X 0)),add_assoc,← Finset.sum_add_distrib]; congr 1; apply Finset.sum_congr rfl; intro i hi; change β*(s^(i+2)*chip X (i+2) y)+s^i*chip Y i y= s^i* Stipend _ _ _ _ _ z; rw (occs:=.pos [1]) [← show (L).symm y=z from (L).symm_apply_apply _,sector p R α hp y]; change β*(s^_ * Radial.jet X _ _)+s^_ * Radial.jet Y _ _=_; rw [pow_add]; have hv := gS β he|>.2; change s^2*β=1 at hv; linear_combination s^i*jet X (i+2) y*hv
end bare
section know
open Kinetic.Port
variable (P:Patch)(K:KernelChoices){a Λ:ℝ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "M"=> Coarse G
variable {ι:Type} [Nonempty ι]
variable (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(U: ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (U i))
    (hO:LocalRatio O)
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
set_option quotPrecheck false
local notation "D"=>topiary P K p O x U Q hx hO F h
variable {i:ι} (hn : Ad G P K n) (J: Tube G (dock P K n)) (hU:J.up=x i)(hT:J.high=p)
    (F₀:Forest (dock P K n).ratio) (l₀:(dock P K n).Choices) {ρ : Bid.Dir G n→ AxisChart G F₀}
open Haiku
include hn hU hT
-- equality across any critical choices through script ages global (off).
lemma crescent (he:Q.Service F₀ p (x i) ρ) (v w: E) : Local.Pure.flip F₀ J O ρ l₀ k v-Local.Pure.flip F₀ J O ρ l₀ k w=D k i n ((L).symm v)-D k i n ((L).symm w) := by
 let R:= x i; let A:=startup F₀ O l₀ R p Q hn (hx i) he hO; let B:= startup T[n] O (label S[n]) R p Q hn (hx i) (h i n hn) hO;
 have He(v:E):= actual_top P K p O x U Q hx hO F h i n hn (k:=k) ((L).symm v); have h0 (v:E): ratePlan A k v = ratePlan B k v:= by
     exact congr_fun (congr_fun (Response.exactly A B (mul_pos (pow_pos hO.scale _) (Real.exp_pos _)) hO hn.1 (fun t=> (toll_main (hx i)).add ((toll_loop (hx i)).scale (t^2))) (mul_pos (pow_pos hO.scale _) (Real.exp_pos _))) k) v
 have hA(v:E): just (preview B) k +D k i n ((L).symm v)= just (Real.log (scaleP (ρ:=ρ) F₀ O l₀ J)) k + Local.Pure.flip F₀ J O ρ l₀ k v:= by
    rw [← He v, ContinuousLinearEquiv.apply_symm_apply]; change ratePlan B k v = _; rw [← h0]; let h' : Q.Service F₀ J.high J.up ρ:=by rw [hT,hU]; exact he
    -- ratePlan expression tied to Startup? need defeq or rw dependent proof
    exact Eq.trans (b:=ratePlan (startup F₀ O l₀ J.up J.high Q hn (show J.up.Bounds J.high a C (U i) from (by rw [hU,hT]; exact hx i)) h' hO) k v) (by cases J with | mk way W w' u q => dsimp only at hT hU; subst p W; rfl) (Response.seed_shadow F₀ l₀ hO J Q hn _ h' ..)
 linarith only [hA v,hA w]
lemma sky (hp : Critical («S»:=dock P K n) F₀ J.high J.up ρ)(r:ℕ)(hg:0<β): S (Local.Pure.script F₀ J O ρ β l₀ r)= S (fun y:E=>∑ j∈ Finset.range (r+1),(gStep β)^j*topiary P K p O x U Q hx hO F h j i n (bend (gStep β) y)):= by
 have hb:J.up.Bounds J.high a C (U i):= by rw [hU,hT]; exact hx i
 obtain ⟨σ,hσ⟩:=Q.graph F₀ hb hn rfl rfl; let A':= Local.Pure.script F₀ J O σ β l₀ r; let b:= gStep β; let G':=Local.Pure.flip F₀ J O σ l₀; let X' (t:E):= bend (G:=G) (n:=n) b t;
 have he (y:E):A' y= Local.Pure.basis F₀ J O σ β l₀ + ∑ j∈Finset.range (r+1), b^j*G' j (L (X' y)):= by nth_rw 1 [← unbend _ y (gS β hg|>.1)]; exact Local.Pure.bookroom F₀ J O σ _ l₀ Q hn hb hσ (L (X' y)) hg -- edit
 rw [Local.Pure.one_frame F₀ J O ρ σ l₀ (Before.Service.is_extension hσ hp)]; ext1 v; change A' v-A' 0= (∑ j∈_, _) -∑ j∈ _,_; rw [he,he,add_sub_add_left_eq_sub, ←Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j hj; change b^j* _-b^j*_= b^j*_-b^j*_; rw [← mul_sub,← mul_sub]; apply congr_arg; have ht:=crescent P K p O x U Q hx hO F h hn J (i:=i) hU hT F₀ l₀ (hU ▸ hT ▸ hσ) (k:=j) (L (X' v)) (L (X' 0)); simpa only [ContinuousLinearEquiv.symm_apply_apply] using ht
end know
end YM.AllOrder.Plateau
