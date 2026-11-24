import YM.LocalTaylorR2.Reset.Register
import YM.LocalTaylorR2.Earned
/-!
# Same support R2 re-expression bills, reaches physical β in a superpolynomial (in χ) mesh accuracy
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Recoil
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org UVExtension
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Song Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato
open Pert Pert.Kinetic Tail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe Roost Opera
variable {G:Gauge} {M: Metals G} {D:Rolls M.p} {A : Alloy M D} {m j N n:ℕ} (R:Factor A) (hp:Mallow.RG12.Earned (railD G) R.shape A.delay) {u:Rep G (A.B.a.S.side (m+1) n)} (H:Guide A.B R.shape N m n u) (O:Return.Wood A.B m n)
local notation "P" => A.B.a.clock
local notation "T" => A.B.a.params m
local notation "b" => A.B.a.budget m
local notation "x" => A.B.a.clock.hatBeta m
local notation "χ" => A.B.a.clock.hatBeta (m+1)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "s!"=> A.B.a.S.side m n
local notation "Z!"=> Song.posting (b) H
set_option quotPrecheck false
local notation "V!"=> plusone H (RG01.Survive.identityX H) Chi.canonical (A.B.kin.alpha N m)
local notation "R₀"=> A.B.kin.path N m
local notation "A₀"=>A.B.kin.alpha N m
local notation "κ"=> A.B.a.clock.forcedAllowance m
local notation "F!"=> Opera.earlyFee (p:=R.expense) A.B N m u.beta

include hp H
open CalendarStep in
lemma paid (hm:m<N): F! ≤2*turnFee b ∧ regularNeed G b (T).clip (T).width (T).paths A₀ F!≤ 2*x ∧ (∀ E : ℝ, 0≤E→ regularNeed G b (T).clip (T).width (T).paths 0 E ≤ χ^(loss Jp/2)*E ∧ (b).threshold*softNeed G b (T).clip (T).width (T).paths 0 E≤χ^(loss Jp/2)*E):=by
    let d:= (R.expense Jp Ip).wanting
    have ht:=Boulevard.suns R.shape A R.inn.chip hm (A.B.a.S.oneStep m n).exact_size H
    have hk:=gatesHere (m:=m) R hp
    have hu : 1≤ betaF G x (D.L Jp):=by rw [← PriceCompiler.beta_eq A.B.valid]; exact (A.B.a.fits.delayed _).le
    have he: F! ≤2*turnFee b:= by
      unfold Opera.earlyFee
      rw [mul_comm 2]; apply mul_le_mul_of_nonneg_left _ (turnFee_pos _|>.le)
      have hH : d≤0:= hk.health.trans (by norm_num)
      have hf := Real.rpow_le_one_of_one_le_of_nonpos hu hH -- maybe name
      have hV := ht.2.1.trans (Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num))
      convert add_le_add hf hV using 1; norm_num
    refine ⟨he,?_⟩; rw [PriceCompiler.beta_eq A.B.valid]
    exact prices hk ⟨rfl,rfl,rfl⟩ (Boulevard.coupling A _ _ hm) he rfl

section current
variable (hG:G.Simple) (hH:Opera.Price A.B R.shape N m n u H)(hm:m<N)(hl:Lives A.B.bake N (m+1) n u)(hb:u.beta∈band A.B.a (m+1))
local notation "τ"=> Song.weighty H Chi.canonical O
local notation "δ"=> (P).allowance m
include hm hl hb
include hG R
omit hp H in
lemma tariff (J:Collection.Listing G s!)(v:Collection.Source G s!)(β τ0 α C K:ℝ)(he:Collection.Local J b v C K):
    Stamped R₀ (T).clip b J v (T).width (T).paths ((P).loopCap m) β τ0 α (regularNeed G b (T).clip (T).width (T).paths α C) K (softNeed G b (T).clip (T).width (T).paths α C) := by
    have hv:=(R.machine.passes hm (Q:=fun _ : ℝ=> u) (l:=Set.univ) (fun _ _=> ⟨hl,hb⟩)).1
    exact stamp he hG (A.B.support.cap N m hm.le) hv.decent hv.width (Return.enough_room ..) β τ0 α
include hp hH
lemma assay {β: Rep G s!} (e0:β.p=b) (e1:β.beta∈ band A.B.a m) (e2:β.Lawful (T).width (T).paths ((P).loopCap m) δ κ)
   (e3: β.eval=earlyValue Z! R₀ (T).clip b V! u.beta τ A₀)
   (hx:(P).monitor m≤ x) (hk:4 ≤ (s!).val)
   (hY:Real.pi^2*(Full.mesh s!)*(2*(Fintype.card PlaqAxes:ℝ)*(2*x)^9) ≤1/2):
    Stamped R₀ (T).clip b Z! V! (T).width (T).paths ((P).loopCap m) u.beta τ A₀ (regularNeed G b (T).clip (T).width (T).paths A₀ F!) κ (softNeed G b (T).clip (T).width (T).paths A₀ F!) ∧
    β.v=Collection.vac V! τ ∧ |β.beta-(u.beta+A₀+Averaging.delta ((Z!).read V!))| ≤ (4*Real.pi^2*coefK*(2*x)^9)*(Full.mesh s!):= by
   have ht:=CalendarStep.grounded R H O hH hm hl hb
   have hC:= tariff R hG hm hl hb _ _ u.beta τ A₀ F! κ ht
   let W:= rest R₀ (T).clip b Z! V! u.beta τ A₀
   have h:Renew β W:=renew hC e3
   have hA:= hC.covers
   have hw : 1<x:=A.B.a.fits.delayed _; have hX:=zero_lt_one.trans hw
   have hf:|β.beta|≤ 2*x:= by rw [abs_of_nonneg (le_trans (half_pos hX).le e1.1)]; exact e1.2
   have hz: Real.sqrt x≥1:= Real.le_sqrt_of_sq_le (by nlinarith)
   have hu:0≤ δ:= Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
   have hr:δ≤1:= Real.rpow_le_one (inv_nonneg.mpr (Real.sqrt_nonneg _)) ((inv_le_one₀ (Real.sqrt_pos.mpr hX)).mpr hz) (by norm_num)
   let e := regularNeed G b (T).clip (T).width (T).paths A₀ F!
   have H0:= base_quote R hp hx hu (hr.trans (by linarith : 1≤ 2*x))
   have h₀: 0≤ e:=by obtain ⟨p,hy,hp⟩:= hA.labels.boundE; exact Cost.nonneg (hp 0)
   have H1:= base_quote R hp hx h₀ (paid R hp H hm|>.2.1)
   have hb' := budget_bound hG h hA e2 (e0.symm ▸ H0) H1 hk hf hY
   haveI:=hG.nontrivial_color
   obtain ⟨c,hc⟩:=exists_norm_eq G.Color one_pos.le
   exact ⟨hC,(priced β W hG e2 hA hk c hc false h).2,hb'⟩
end current
end YM.LocalTaylorR2.Recoil
