import YM.AllOrder.Plateau.Stamp
import YM.AllOrder.Haiku.Psalm
/-!
# Uniform support approximations BEFORE physical cost schedule. Constant on mesh,
coded at actual scale; this version analytically P.Val. Uniform all powers & cuts off. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll
open AbsoluteSums Fare Shellac Work.G05
open Haiku Haiku.Coat Fire PertExtension.Series Radial PertExtension PositionX.Gauss PositionX.Jet
open Laplace Laplace.SigmaP Response Ink Ink.Method Laurent Stationary Ink.Rail
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n : Side} {k j w N : ℕ}
variable {σ C Z D β z:ℝ}
local notation "E"=>Positions (Primary n G)
local notation "L"=>Kinetic.Port.exteriorL G n
section plan
variable {ι: Type} [Fintype ι] {f:Positions ι→ℝ} (H : Prices k C f)
include H
lemma ticketR (x:Positions ι)(v:Fin j →ι) : ‖entry f x v‖ ≤ C*pullC j k * (1+‖x‖)^k := by
 induction j generalizing k C f with
 | zero=> unfold pullC entry; rw [iteratedFDeriv_zero_apply,mul_one]; exact H.2.2 x
 | succ y ih=>
    let j:= v (Fin.last y); let u:= diff' (Push.Uniform.bolt j) f; let W(i:Fin y):=v i.castSucc; let L':= ContinuousLinearMap.apply ℝ ℝ (Push.Uniform.bolt j); have hv:= ih (H.taper (Push.Uniform.bolt j) (norm_bolt j).le) W; rw [← show entry u x W= entry f x v from ?_]; swap; · unfold entry; rw [show u=L' ∘ fderiv ℝ f from rfl]; rw [L'.iteratedFDeriv_comp_left (H.2.1.read.smooth.contDiffAt.fderiv_right (m:=ω) (by simp)) le_top, iteratedFDeriv_succ_apply_right]; rfl
    rw [mul_assoc C] at hv; refine hv.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) (by omega)) (mul_nonneg H.1 ((pullC_pos (y+1) k).le))) -- rw position? test
omit H
lemma pricedBend {p:Link G n→ℝ} {b:ℝ}(h:Prices k C p)(hb:0<b): Prices k (C*(1+b⁻¹)^k) (fun x:E=> p (bend b x)):= by
 let g:=bendL (G:=G) (n:=n) b -- syntax
 simp_rw [curve]; refine ⟨mul_nonneg h.1 (by positivity),h.2.1.lead g,fun i=>?_⟩
 let s:= ‖i‖; let u:= (L).symm i; have hp:‖u‖≤‖i‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j=> norm_le_pi_norm i (Primitives.TwoWave.RealSlice.outsider G n j) -- namespace
 have hs:‖g i‖≤ b⁻¹*s:=by change ‖b⁻¹ • u‖≤_; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; gcongr
 refine (h.2.2 (g i)).trans ?_; rw [mul_assoc, ← mul_pow]; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) h.1; change 1+ ‖g i‖≤ (1+b⁻¹)*(1+s); have ht:0≤ s:= norm_nonneg _; nlinarith only [ht,hs, show 0≤b⁻¹ from inv_nonneg.mpr hb.le] -- norm
include H
lemma brushLens (u:Positions ι)(hx:‖u‖ ≤ z)(hd:z<1) (h:1≤D)(hD:(Fintype.card ι:ℝ)≤D)(j:ℕ) : Brush j (tollS D j (C*mantle j k *2^k)) 1 f u:= by
 have hm:0 ≤ mantle j k:= (pullC_pos 0 k).le.trans (can_pull 0 k _ (Nat.zero_le _)); refine Brush.offer.2 ⟨H.2.1.read.smooth.contDiffAt.of_le le_top, fun i hi=> raises h hD (by have hh:=H.1; positivity) hi (fun v=> ?_)⟩; refine (ticketR H u v).trans ?_; refine mul_le_mul (mul_le_mul_of_nonneg_left (can_pull i k j hi) H.1) (pow_le_pow_left₀ (by positivity) (show 1+‖u‖≤2 by linarith) k) (by positivity) (mul_nonneg H.1 hm)
end plan
section loose
variable (p:Clip)(R:PathData G)(α:ℝ)(hp:R.Bounds p σ C Z)
    {y e : ℝ} (ha:0<y)(hf:y<1)(hu:1≤D)(hD:(Fintype.card (Primary n G):ℝ)≤ D)
variable (x:Positions (Primary n G))(hx:‖x‖≤y)
local notation "T₀"=> staff p R n
local notation "Q₀"=> drift p R α n
local notation "F"=> PhysicalNext.Repeat.Shellac.off
def edges (A:BareRates.pre G σ C k) (p:Clip) (D Z α e:ℝ)(j:ℕ) := (tollS D k (BareRates.bill A p)*2*e^(j+3), tollS D k ((1+|α|+Z)*BareRates.bill A p)*2*e^(j+1))
@[simp] lemma skirt {X Y:Type}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ X][NormedSpace ℝ Y] (f g:X→Y): F (f-g)= F f-F g:= by ext1 x; change (f x-g x)-(f 0-g 0)=(f x-f 0)-(g x-g 0); abel -- include issue
include hp ha hf hu hD hx
lemma corners (A:BareRates.pre G σ C k)(j:ℕ)(hj:j+3≤k): Brush k (edges A p D Z α y j).1 y⁻¹ (F (T₀-blockTaylor (j+2) T₀)) x ∧ Brush k (edges A p D Z α y j).2 y⁻¹ (F (Q₀-blockTaylor j Q₀)) x := by
 have h(u:E)(h:u∈ball 0 1):= bareSocket _ A hp h α; let f:= T₀; let g:= Q₀; obtain ⟨hX,hQ,hV,H₀,h0,h'⟩:= h 0 (mem_ball_self (by norm_num)); have hc := hasInheritance hp; have hC:1≤k:=by omega
 have he(u:E)(hh:u∈ball 0 1) : Brush k (tollS D k (BareRates.bill A p)*(1+1)) 1 (F f) u ∧ Brush k (tollS D k ((1+|α|+Z)*BareRates.bill A p)*(1+1)) 1 (F g) u:= ⟨(horizonB hu hD H₀.le hV zero_lt_one hC hh (fun i hi=> ⟨(h i hi).2.2.2.2.1,(h i hi).1⟩)).2, (horizonB hu hD (by positivity) hV zero_lt_one hC hh (fun i hi=> ⟨(h i hi).2.2.2.2.2,(h i hi).2.1⟩)).2⟩
 rw [skirt,skirt, ←taylor_off _ _ ((cursor p R α hp A _ (mem_ball_self zero_lt_one)).1.of_le le_top),←taylor_off _ _ ((cursor p R α hp A _ (mem_ball_self zero_lt_one)).2.of_le le_top),edges]; dsimp only [Prod.fst,Prod.snd]; rw [show (2:ℝ)=1+1 by norm_num]; exact ⟨Local.Taylor.forecast ha hf.le hj (fun i hi=>(he i (mem_ball_zero_iff.mpr (hi.trans_lt hf))).1) hx, Local.Taylor.forecast ha hf.le (by omega) (fun i hi=>(he i (mem_ball_zero_iff.mpr (hi.trans_lt hf))).2) hx⟩
omit hp
variable (A:Packet G N)(hs:0<σ)(hb: SumBudget (fun i=>(A i).budget σ) C)(hZ:PaintSupply G k Z) -- width Fore
local notation "Ψ"=> speak A n
omit ha hf hu hD hx in
lemma ratioW_pos (i j:ℕ)(he:0<e):0<ratioW e i j:= by unfold ratioW; positivity
-- lower= e's perturb cost order, output ≤ j, compare after turning.Here ambient size b. ratioW actual hold
abbrev shin (G:Gauge)(σ C D Z y:ℝ)(k N j l B:ℕ) :=tollS D k (C*Plateau.amt G N k σ Z)*2*y^(j-l+N+1)+ tollS D k ((Real.exp (-(σ/2)*B)*C)*Plateau.amt G N k (σ/2) Z)*2
include hb hs hZ
lemma cuts (b:ℝ)(hd:0<b)(B:ℕ)(l j:ℕ)(he:j-l+N+1≤k): Brush k (ratioW b l N * shin G σ C D Z y k N j l B) y⁻¹ (F (ratioW b l N • (blockTaylor (j-l+N) Ψ - speak (crop B ∘ A) n))) x:= by
 let U:= ratioW b l N; let f:=Ψ; let f':= speak (crop B ∘ A) n; let g:=speak (leaf B ∘ A) n; let T:=blockTaylor (j-l+N) Ψ; have h₁ : f-f'=g:= funext fun i=> post_bill A hs hb B (represent (tint G _ i));
 have h:1≤k:=by omega
 rw [off_sc]; have ht:0< U:= ratioW_pos l N hd; let p:=tollS D k (C*Plateau.amt G N k σ Z)*2*
        y^(j-l+N+1); let P:=tollS D k ((Real.exp (-(σ/2)*B)*C)*Plateau.amt G N k (σ/2) Z)*2
 have hr: F (T-f')= -(F f-blockTaylor (j-l+N) (F f))+ F g:= by
    rw [taylor_off f (j-l+N) ((signal A hs hb hZ _ (mem_ball_self zero_lt_one)).1.of_le le_top),skirt,← h₁,skirt]; unfold T f; abel
 have h3: Brush k p y⁻¹ (F f-blockTaylor (j-l+N) (F f)) x:=Local.Taylor.forecast ha hf.le he (fun i hi=>speaking A hs hb hZ h hu hD i (mem_ball_zero_iff.mpr (hi.trans_lt hf))) hx
 have h2:= speaking (leaf B ∘ A) (half_pos hs) (Plateau.release A hs hb B) hZ h hu hD x (mem_ball_zero_iff.mpr (hx.trans_lt hf)); change Brush k (U* (p+P)) y⁻¹ (U • F (T-f')) x; rw [hr]; rw (occs:=.pos [1]) [ ← Real.norm_of_nonneg (show 0≤U from ht.le)] -- rw all U !! choose occ
 exact (h3.opposite.gathering (h2.climb le_rfl ((one_le_inv₀ ha).2 hf.le))).smul U
end loose
end YM.AllOrder.Plateau
