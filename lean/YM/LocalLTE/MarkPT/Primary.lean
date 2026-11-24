import YM.LocalLTE.FieldPT.Purchase
/-! Analytic power aggregated investment -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals Averaging
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ}
open Coup Scarf East LocalLTE.Fan Pastel
open Collection.Price LocalLTE.FrameBox Progress.DirectedRecipe YM.LocalLTE Weft Scene
section stage
variable (X D) (K j M r:ℕ) {ε η:ℝ} (C:Targets X.p X.K) (Z:Expenses C) (w:Return.Wages) {V:ℕ→ℝ} (R:Register D Z w V) (δ:Wind p0 η) (b:ℕ→ℕ→ℝ)(f:ℕ→ℕ→ℕ) (k:ℕ→ℕ→ℕ→ℕ)
local notation "A'" => X.p
-- receipts robust under Matter.j.B.Update.Declarations.* abstract buy before Build
section gauge
variable {X D} (i j:ℕ) (t B κ ε:ℝ)
local notation "L"=> D.L i
local notation "S"=> X.p.profile j
local notation "Y0"=> (betaF G t L)
local notation "b'"=> bandTotal K δ k i j
set_option quotPrecheck false
-- output after-L with charges not exceeding declared β output permit g target.Noclaims.
-- surplus ηLoss 
variable (e:ℝ) (K:ℕ)
variable (hk:Weft.Scene.trackPower M ≤ K)(hp:0< ε)(he:ε< ((r+1:ℕ)-e)/2)(h:0< b i j){q:ℝ}(hκ:Reliable G κ q)
include hκ hk hp he h
lemma playT : ∃ F:ℝ→ℝ, Rate G (D.L i) 0 F ∧∀ᶠ x in atTop, ∃ d :ℝ,∃ p:ℕ→ℝ, DawnX M r C Z w R δ b f k i j x κ ε e K (F x) d p:=by
    let F:= X.p.profile j; obtain ⟨P,hP,H'⟩:= readings G M (D.L i) κ hκ K hk; have h₀ : ∀ᶠ x in atTop,0 ≤ P x := H'.mono fun x hx=>hx.1
    choose u v a p c hu hv ha H hc hT using fun t=> Mallow.asks C Z w R δ b f k i j κ ε P K hP h₀ h hp hκ t M
    let w':ℝ:= -(1/2:ℝ)*(r+1:ℕ)+ε; let W n t:= Price.glowing (bandTotal K δ k i j n) (pie n+1) r (betaF G t (D.L i)) ε* p n t
    have hw (n:ℕ):Rate G (D.L i) w' (W n):=by unfold W Price.glowing; simpa only [add_zero] using! (((Rate.power (G:=G) («L»:=D.L i) (a:=w')).mul_left _).mul (H n))
    let d(t:ℝ):=∑ i:Fin (M+1),|W i t|
    have hz:Rate G L w' d:= by
         have he (Z:Finset (Fin (M+1))): Rate G L w' (fun t=>∑ i∈Z,|W i t|):=by
             induction Z using Finset.induction_on with
             | empty=> intro z _; filter_upwards [Delay.shift_pos G (D.L i)] with t ht; simp only [Finset.sum_empty, abs_zero]; positivity
             | insert t Z hz h=> simp_rw [sum_insert hz]; exact (Brim.absolut (hw t)).add h
         exact he univ
    have hL := Urns.actualG L e _ _ (((hz.mul_left 2).mul_left (turnFee (Time.probe F))).mul_left (↑(M+2:ℕ):ℝ)) (by unfold w'; linarith)
    have hV n: ∀ᶠ t in atTop,∀ β:ℝ, let Y:=betaF G t (D.L i); β∈Icc (Y/2) (2*Y) → Price.scaleFee (bandTotal K δ k i j n)*(c n t)*gStep β^(r+1)≤ gStep β^e:=by
       let P':=Price.scaleFee (bandTotal K δ k i j n); let w' t:=(P' * |c n t|)*(2*gStep (betaF G t L))^(r+1)
       have hx':=actualG L e _ _ ((Brim.absolut (hc n)|>.mul_left P').mul ((Sienna.glim G L).pow (r+1))) (?_); swap; · push_cast at *; linarith only [hp,he]
       filter_upwards [hx',Delay.shift_pos G L] with t ht hp β Y hb; obtain ⟨hf,hb'⟩:= Sienna.lamp G L hp β hb.1
       apply (mul_le_mul (mul_le_mul_of_nonneg_left (le_abs_self _) (Price.carteF _)) (pow_le_pow_left₀ hf.le hb' (r+1)) (pow_nonneg hf.le _) (mul_nonneg (Price.carteF _) (abs_nonneg _))).trans (ht _ hb.1 hb.2)
    refine ⟨P,hP,?_⟩; filter_upwards [H',eventually_all.mpr (fun t:Fin (M+1)=> (hT t).and (hV t)), hL, (YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,(Sienna.glim G L).below (by norm_num) 1 zero_lt_one, hP ε hp,eventually_all.mpr (fun i:Fin (M+1)=> H i ε hp) ] with x hp hv hh hy hG hV hT
    have he:0 < betaF G x L:= zero_lt_one.trans_le hy
    refine ⟨d x,fun n=> p n x,hp.1,hy, Finset.sum_nonneg (fun i _=>abs_nonneg _),fun β h=>?_ ,fun n hn=>?_,fun p hP β hβ=>?_,hp.2,hV,fun i h=> hT (⟨i,by omega⟩:Fin (M+1))⟩
    · obtain ⟨hz,h'⟩:= Sienna.lamp G L he β h.1; exact ⟨hz,h'.trans ((le_abs_self _).trans hG)⟩
    · let i':Fin (M+1):=⟨n,by omega⟩; exact ⟨u n x, v n x, a n x, c n x,hv i'|>.1,( (le_abs_self (W i' x)).trans (Finset.single_le_sum (f:=fun i:Fin (M+1)=>|W i x|) (fun i _=>abs_nonneg _) (mem_univ i'))), (hv i').2⟩ -- hO order
    have he:turnFee p=turnFee (Time.probe F):= by obtain ⟨h₁,h₂,h₃⟩:=hP; unfold turnFee Push.Local.turnCost; rw [h₁,h₂]; rfl
    rw [he]; exact hh β hβ.1 hβ.2
end gauge
-- pp order.out resources.Pre-L inputs.
end stage
end YM.PhysicalNext.Repeat.Mallow
