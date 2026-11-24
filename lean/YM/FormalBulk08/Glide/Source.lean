import YM.FormalBulk08.Glide.Clam

/-! Actual input single-mover from prepared Gaussian square. Locate via
all periods, including test alignment on absolute links. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Glide
open Chapel Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava Bank Stationary Tree Work.F05
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C D : ℝ}{j t:ℕ} {n : Side}{I J Q : Type}
variable (F: Flight j t)(V : Lodge F.patch)

def limn (G:Gauge)(K:KernelChoices):= composeRows (winging (Rim G F.patch) (Loc G 1)) (composeRows (pane G F.patch V) (zealand K F V G))
def script (G: Gauge)(K:KernelChoices): Cross F.L (Loc G 1) (Loc G 1):= fun i j=> limn F V G K i (.inr j)
lemma script_acts (G:Gauge)(K:KernelChoices)(v k): (script F V G K).acts n v k= (limn F V G K).acts n v (coastRight _ _ _ k) := rfl

lemma limn_pay {K:KernelChoices} (h : (locating G K F V).strip η A) (hp:0≤η):
    (limn F V G K).strip η ((Fintype.card (Board G F.patch))* (1 * (Fintype.card (BoardL G F.patch V)*(1*max 1 A)))):= strip_compose hp (wing_strip _) (strip_compose hp (pane_pay V _) (zealandPay K F V h))
lemma script_pay {K:KernelChoices} (h : (locating G K F V).strip η A) (hp:0≤η):
    (script F V G K).strip η ((Fintype.card (Board G F.patch))* (1 * (Fintype.card (BoardL G F.patch V)*(1*max 1 A)))):= fun i j=> limn_pay F V h hp i (.inr j)

lemma wing_eval (n:Side)(P:Patch)(a: Tor n (Rim G P)) (y: Tor n (Board G P)) :
   (winging (Rim G P) (Loc G 1)).acts n a y= if y=(a.1,Sum.inl a.2) then 1 else 0:= by
   rcases y with ⟨x,u|b⟩
   · rw [show _ = _ from (show (winging (Rim G P) (Loc G 1)).acts n a (x,Sum.inl u)=(unitRow _).acts n a (x,u) from rfl)]; rw [acts_unit]; rcases a with ⟨v,c⟩; simp [Matrix.one_apply,eq_comm]
   simp [Row.acts,winging]
lemma inscrip (G : Gauge)(K:KernelChoices)(n:Side)(hp: (Flight.duo K.penalty F).A0.strip σ A)(h:0<σ)(ha:0≤A):
   let S:= primary F.patch K n; let T:= V.forest (S:=S)
   installed S.ratio (script F V G K)=(dropRoot G S T)ᵀ * pMean G K F n T := by
    intro S T;obtain ⟨C,hC,H⟩:=Lodge.bothPay G K V _ h; have hh:(locating G K F V).strip σ (C*A) := (H _ A ha hp).1
    let Y:=pane G F.patch V;let Z:=zealand K F V G; let v:=limn F V G K; have hY:Y.strip σ 1:=pane_pay V _; have hZ: Z.strip σ (max 1 (C*A)):=zealandPay K F V hh
    have he (a:Tor n (Rim G F.patch))(b: Tor n (BoardL G F.patch V)): v.acts n a b=(Y.acts n *Z.acts n) (a.1,Sum.inl a.2) b := by
       unfold v limn; rw [acts_compose h.le (wing_strip σ) (strip_compose h.le hY hZ), acts_compose h.le hY hZ];rw [Matrix.mul_apply]; simp_rw [wing_eval]; rw [Finset.sum_eq_single (show Tor n (Board G F.patch) from (a.1,Sum.inl a.2)),if_pos rfl,one_mul]; intro x _ hx; rw [if_neg hx,zero_mul];simp
    ext1 i k; let a:=unitSplit G S 1 i
    change (script F V G K).acts n a k = _; rw [script_acts, show (limn _ _ _ _).acts n _ _=_ from he a _]
    change (Y.acts n * Z.acts n) (staging G S (Sum.inl i)) (saddleP G S V (Sum.inr k)) = _
    rw [Matrix.mul_apply]
    let e:= saddleP G S V
    rw [← Equiv.sum_comp e (fun j=> Y.acts n (staging G S (Sum.inl i)) j* Z.acts n j _)]; apply Eq.trans (Finset.sum_congr rfl ?hh) ?b
    case hh=> intro x _; rw [show Y.acts _ _ _=_ from true_pane S V (Sum.inl i) x, show Z.acts _ _ _=_ from twig F V n σ A h ha hp x (Sum.inr k)]
    case b=> rw [Fintype.sum_sum_type,Matrix.mul_apply]; simp [matPane, outshift]; rfl
end YM.FormalBulk08.Glide
