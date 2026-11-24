import YM.FormalBulk08.Glide.Source

/-! Dispense from Ward kernel. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Glide
open Chapel Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava Bank Stationary Tree Work.F05
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C D : ℝ}{j t:ℕ} {n : Side}{I J : Type}
variable (F: Flight j t)(V : Lodge F.patch) {K:KernelChoices} (hp: (Flight.duo K.penalty F).A0.strip σ A)(h:0<σ)(ha:0≤A)
lemma copper {S:Row I J}{B:ℝ}(hR:S.strip σ B)(he:0≤σ)(x : Biglot I)(y:Biglot J): Tendsto (fun n=> S.acts n (Lotus.drip n x) (Lotus.drip n y)) atTop (𝓝 (lands S x y)):= landing_row S (Row.rights _ _ hR he) x y
variable (G K)
lemma wheat (f:Side)(x : Site f)(a: Axis)(b:G.ColorIndex) {s: Type*} (U: Matrix (Lines G f 0) s ℝ) (u:s) : (patron G (d 0 f)*U) (x,coord a,b) u=U (x+step a,vac,b) u-U (x,vac,b) u:= by
    let v : Stationary.BaseSites G f:=fun i=>U i u
    change (patron G (d 0 f)*ᵥ v) _= _; rw [patron_fee, ←first_uniform];exact congr_fun (congr_arg WithLp.ofLp (gradientC v x a)) b
variable {G K}
def chair (G: Gauge)(K:KernelChoices) := grown G (Flight.duo K.penalty F).A0
lemma owner {S : Cross F.L I J}{B:ℝ}(k:KernelChoices)(X:S.strip σ B)(he:0≤σ)(x:Biglot I)(y:Biglot J):
    Tendsto (fun n:Side=> installed (primary F.patch k n).ratio S (Lotus.drip (n*F.patch.L) x) (Lotus.drip n y)) atTop (𝓝 (merit S x y)) := by
    have hh:= copper X he (Bank.scroll F.patch.L I x) y; refine hh.congr' (.of_forall fun n=> ?_)
    exact congr_arg (fun p=> Row.acts S n p (Lotus.drip n y)) (scroll_pull x (primary F.patch k n).ratio)
include hp ha h
lemma literal (G: Gauge): trench (minusRows (script F V G K) (chair F G K)) (roots G K F V) := by
   intro x a i b
   obtain ⟨Z,hZ,H⟩:= Lodge.bothPay G K V _ h
   obtain ⟨hx,hW,hK⟩:=H _ _ ha hp; let S := chair F G K;let R:= script F V G K; let U:=roots G K F V
   have hR:R.strip σ _:=script_pay F V hx h.le; have hS:S.strip σ A:=grown_budget G _ ha hp
   have hl(n:Side): installed (primary F.patch K n).ratio R= installed (primary F.patch K n).ratio S + patron G (d 0 (n*F.patch.L))*installed (primary F.patch K n).ratio U := by
       obtain ⟨hr,he⟩:= hK n; let T:= primary F.patch K n
       refine Eq.trans (inscrip F V G K n hp h ha) ?_; refine Eq.trans he ?_; exact congr_arg (· + (patron G (d 0 (n*F.patch.L))*installed T.ratio U)) (grown_act (S:=T) (G:=G) (Flight.duo K.penalty F).A0).symm
   have he n: installed (primary F.patch K n).ratio (minusRows R S)= patron G (d 0 (n*F.patch.L))*installed (primary F.patch K n).ratio U := by
       have hEq: installed (primary F.patch K n).ratio (minusRows R S) = installed (primary F.patch K n).ratio R-installed (primary F.patch K n).ratio S:= by
           ext a b; exact congr_fun (congr_fun (acts_minus h.le hR hS n) (splitCo (primary F.patch K n).ratio _ a)) b
       exact hEq.trans (sub_eq_iff_eq_add.mpr ((hl n).trans (add_comm ..)))
   let v:edgeL G:=(x,coord a,i); let t:Biglot (spots G):=(x,vac,i); let q:Biglot (spots G):=(x+ step a,vac,i)
   have hZ:= owner F K (strip_minus hR hS) h.le v b; have hy:= owner F K (S:=U) hW h.le
   apply tendsto_nhds_unique hZ (((hy q b).sub (hy t b)).congr' (.of_forall fun n=> ?_)); symm; refine Eq.trans (congr_fun (congr_fun (he n) (Lotus.drip (n*F.patch.L) v)) (Lotus.drip n b)) ?_
   have Hn:= wheat G (n*F.patch.L) (wrap (n*F.patch.L) x) a i (installed (primary F.patch K n).ratio U) (Lotus.drip n b); have hy: Lotus.drip (n*F.patch.L) q = (wrap (n*F.patch.L) x+step a,vac,i):=Prod.ext (by simp only [q,Lotus.drip, map_add, wrap_step]) rfl
   exact Hn.trans (congr_arg (fun p=> installed (primary F.patch K n).ratio U p (Lotus.drip n b)-installed (primary F.patch K n).ratio U (Lotus.drip (n*F.patch.L) t) (Lotus.drip n b)) hy.symm)
end YM.FormalBulk08.Glide
