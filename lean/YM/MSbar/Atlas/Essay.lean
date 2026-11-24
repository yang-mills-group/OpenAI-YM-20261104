import YM.MSbar.Atlas.Epoch
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f n':Side}{n:ℕ}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk Finset
-- Numbers set for each {stage pair,p order}; look-ahead delays called eventually after L.
variable (P: Patch)(K : KernelChoices)(J:Voice G) (A B:Stage)(p:Palisade) 
set_option quotPrecheck false
local notation "L"=> P.L
local notation "Ξ"=> tip G L
variable {R:Rep G f}{Y:Rep G c}
local notation "Vu"=> (represent (G:=G) (n:=c) ∘ tint G (Exterior.Body 1 c))
variable (i:S.Choices)(F:Forest S.ratio)(j:Key F G)(s:ℝ)(x:Positions (Primary c G))
local notation "κ"=>tip G P.L s
local notation "t"=>radiusB κ
local notation "E!"=> stockMove G p κ
local notation "e"=> increments κ
local notation "d" => distance κ
local notation "N"=> digits G p κ
local notation "T'"=> hurry p (max (skies κ) (arch κ)) E! (2*winch κ)
variable (htb:S.patch=P)(hq:S.kernel=K)
open Metric Set
variable {β D E d₀:ℝ} (hm:Season J A B s R Y S D)(hb:Tinted A B s P K p J R Y D E d₀)
namespace Tinted
variable (h:Grants i R F p n)(g:Clear G J)

include g h hb hm htb hq
lemma business (ht:0≤D)(hh:0 ≤ E)(τ₀:ℝ) (hW: ‖x‖ ≤ skies κ)(he: |τ₀|= e) : chance S R (Vu x) (tailsSet F J i j τ₀ x R (3*(increments κ*distance κ))) ≤ Real.exp (rpay κ*(N))+ ↑(N)*E:=by
    have hx:=hb.hues τ₀ he; let W:=Vu x; let k:= shutterPad F G j (t);let r:=halo (2*t) k; let σ:= youth F r; let b:=(Vu x); let Lb:= sizingW K*κ
    let fN:= (belt (t):ℝ); let Qv :=  (Lattice.box (macroR P)).card*D+d₀; let Q:=fN*(D+(4*Qv)) -- shadow
    have hv: W∈ calm G c (base J κ):= litV P K J p A B s x hb g hW _ rfl hx.arc
    have hp':=stencilSizes P K J p F j A B s x htb hq hm hb g hW ht hx.arc _ rfl -- order inspect
    have hm':=hm.case_;have hmC:=hm.hull; rw [htb] at hm'; let Θ:=hm'.lawful
    have hg:0<κ:=zero_lt_one.trans hb.room; have hd':0 < d:= by unfold distance; have hz:=Real.log_pos hb.room; positivity
    have hQ:0 < increments κ := Real.rpow_pos_of_pos hg _; have hy :0<E!:= by unfold stockMove steps; have he:=wi G p; positivity
    have hS:=voids hv hb.holm; have hc:0<S.push R.beta R.eval W:= by rw [←hm.taskEval]; unfold Rep.eval; rw [Activities.gas_one _ _ hS, mul_one]; exact Real.exp_pos _
    have H: Admitted (Vu x) R S B.width B.paths (ability κ) (lbt κ) 1:=⟨hm'.lawful,fun i=> (hm.shine _|>.le),hc,S.isKernel hm.bends.1 _⟩; have hT:= hm.cuff; rw [htb,hq] at hT
    have hz:0≤ R.beta:= (by linarith only [hm'.beta,hg])
    have hk : k.card ≤ skirt (t):= by unfold k shutterPad; simpa only [skirt,Finset.card_singleton,one_mul] using Corona.halo_size ({address F G (Sum.inr j)}: Support f) (t)
    have ha: r.card ≤ belt (t):=le_trans (Corona.halo_size k _) (Nat.mul_le_mul_right _ hk)
    have hpu: R.p.B=t:= hm'.size
    refine lap (u':=increments κ*distance κ) F J p i j τ₀ (t) x h g hm.bends.1 hx (by rw [htb]; exact hb.cover) hv hW (?_) (κ*sizingW K) hT H hz hm.storm hm.primal (hpu ▸ hm'.decent.radius) hpu.le hm'.decent hm.lights hm.shine hS ht hp' (N) (show rpay κ ≤ 0 from by unfold rpay; apply neg_nonpos.mpr; positivity) ?_ hy.le (hb.walk _ hk) ?_ hh
    · refine le_trans ?_ hb.bon; change bonfire F _ r _ _ ≤ _; unfold bonfire; apply mul_le_mul_of_nonneg_right _ hx.warmth; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (zero_le_one.trans g.cost) (hx.warmth.trans hx.step)); gcongr
    · have hx : (digits G p κ:ℝ) ≤ d/E! := Nat.floor_le (div_nonneg hd'.le hy.le); have hz:= (le_div_iff₀ hy).mp hx; have hb:= mul_le_mul_of_nonneg_left hz hQ.le; rw [he]; linarith only [hb, mul_nonneg hQ.le hd'.le]
    have hv : σ.card ≤ vestal P t:=by
       let I:= 4*S.patch.L.val+8; refine le_trans (show σ.card≤ r.card*skirt I from Corona.halo_size r I) ?_; unfold I; rw [htb]; exact Nat.mul_le_mul_right _ ha
    apply le_trans ?_ hb.adapts; change (1+Real.exp _) * Q + D*(R.p.mass σ 2*Real.exp (σ.card*1:ℝ)) ≤ _
    have hP : xBill R.p (σ.card) 1 ≤ xBill R.p (vestal P t) 1 := by unfold xBill; gcongr; exact R.p.exponent_pos.le
    have he:R.p.mass σ 2 ≤ Real.exp (R.p.supportExponent*σ.card)*2:=by
       -- coverNumber ≤ card only if contiguous; sphere union. use bound by own contiguous structure.
       unfold BudgetPoint.mass; gcongr; exact R.p.exponent_pos.le
       let P':=R.p.B
       have h(X:Support f)(n:ℕ)(h: Corona.Ships X 1): Corona.Ships (halo n X) 1 := Corona.ship_halo n fun i hi j hj=>Relation.ReflTransGen.mono (fun u v (ht : Corona.Touch X 1 u v)=>⟨ht.1,ht.2.1,(ht.2.2).trans (by omega)⟩) i _ (h i hi j hj) -- type
       apply Corona.list_cost _ (D:=σ); refine ⟨halo_subset .., h σ P' (h _ _ (h _ _ (Corona.ship_halo (t) fun i hi j hj=>?_)))⟩; rw [Finset.mem_singleton.mp hi, Finset.mem_singleton.mp hj]
    have hF : 0≤Q:= (chance_pos H (vital F r _ _ (G:=G)|>.from_here.compl)).trans hp'
    apply add_le_add (mul_le_mul_of_nonneg_right ?_ hF) (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right he (Real.exp_pos _|>.le)).trans hP) ht)
    apply add_le_add_right; apply Real.exp_monotone; apply add_le_add_left; change _*(4*(k.card:ℝ)) ≤ _*(4*_); gcongr
    all_goals exact mul_nonneg hT.cost (mul_nonneg (zero_le_one.trans g.cost) hx.warmth)
end Tinted
end YM.MSbar.Heath.Stock
