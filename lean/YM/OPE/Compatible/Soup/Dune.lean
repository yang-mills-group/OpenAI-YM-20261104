import YM.OPE.Compatible.Soup.Vow
import YM.OPE.Compatible.Soup.Price
import YM.OPE.Compatible.Tony.Baba
import YM.OPE.Compatible.Lamb.Reek
/-!
# Annual statistics. Working rank budgets through order 5
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset Sleeve
open Silt Libra Coin Rill Silt.Float Variance Votive PertExtension Series GaussianScore Radial Next.Foundations
variable {G:Gauge}{b i j k r:ℕ}{n:Side}
variable {v s a c:ℝ}{p:Clip}{Z:PathData G}
open Next.Free Next.Scheduling
open UVNext.CouplingReset BetaTransport
variable {K:Sponsor G}{T:Seasons K}
lemma census_unit (x:PathData G)(p:Clip)(P:BudgetPoint) (n:Side):mainTerm p x (1:Config G n)=0∧Precision.loop x (1:Config G n)=0:=by
        obtain ⟨h,hp,H⟩:=unmasked_precision x p (flags_one P (G:=G) (n:=n)); rw [← h,← hp]; exact ⟨kinetic_one .., UVNext.CouplingReset.loop_one ..⟩
lemma duneV (A:Alps K T i c)(P:BudgetPoint)(x:Bid.Dir G n) : Dune A x= mainTerm A.clip A.live (represent x):=by rw [Kope, CircP, (census_unit A.live A.clip P n).1,sub_zero]
lemma ciel (A:Alps K T i c)(P:BudgetPoint)(x:Bid.Dir G n)(v:ℝ)(h:flags P.threshold (represent x)=∅): A.live.inChannels A.clip P v (represent x)= v*Dune A x+Rh A x:=by
       obtain ⟨he,hp,H⟩:= unmasked_precision A.live A.clip h; rw [channels_split,duneV A P x,he,hp]; rfl
lemma unit_at (A:Alps K T i c)(P:BudgetPoint)(n:Side):Dune A (0:Bid.Dir G n)=0∧Rh A (0:Bid.Dir G n)=0:=by rw[duneV A P]; change mainTerm _ _ _=_ ∧ loop _ _=_; rw[Precision.link_one]; exact census_unit A.live A.clip P n
lemma perch_kind (q:Clip)(hs:0<s)(ha:0≤a):∃ f t H:ℝ,0≤f∧0<t∧0≤H∧∀ (n:Side)(_P:BudgetPoint) (c Y W:ℝ)(A:Alps (G:=G) K T i c), A.clip=q→ A.live.Bounds q s a Y→∀ (b:ℕ)(x:Bid.Dir G n),SerT x b→‖x‖ < W→Past (Dune A) x k W (f*Squad b t)∧Past (Rh A) x k W (H*Y*Squad b t):=by
       obtain ⟨t,ht,h⟩:=sesh (s/2) (half_pos hs) k; obtain ⟨d,hd,D⟩:=atlasK G q s a hs ha k t ht h; obtain ⟨f,hf,H⟩:= atlasY G s hs k t ht h; refine ⟨d,t,f,hd,ht,hf,fun n p c Y W A hp hh b x hx hw=>?_⟩; let g:=waterV (oathV A.live q) (N:=n); have he : Dune A (n:=n)=fun x=> mainTerm q A.live (represent x):=funext fun x=> (duneV A p x).trans (by rw [hp]); rw [he]; have hy:0 ≤Y:= (tsum_nonneg hh.two.1).trans hh.two.2.2
       exact ⟨pastV _ (D _ Y hh) hd ht x hx hw (mainTerm _ _) (funext fun V=> oath_main V hh),pastV _ (H _ _ _ _ hh) (mul_nonneg hf hy) ht x hx hw _ (funext fun V=> oath_trail V hh)⟩ -- f lambda explicit
lemma squad_pos (b:ℕ)(s:ℝ): 0 ≤ Squad b s:=by unfold Squad; exact mul_nonneg (by positivity) (tsum_nonneg fun i=>by unfold Next.Scheduling.decay; positivity)
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{p:E→ℝ}{x:E}{u Z:ℝ}
open Set
lemma Pat_charge (H:ContDiffAt ℝ ω p 0)(h:Past p x k a u)(hi:0 < i)(he:i ≤ k)(_ha:0 ≤ a)(_hu:0≤u): ‖jet p i x‖ ≤ a^i*u:=by
        let g(y:ℝ):=p (y • x); have hv:= h.2 i hi he 0; change ‖iteratedDeriv i g 0‖ ≤ _ at hv
        have hx: iteratedDeriv i g 0=iteratedFDeriv ℝ i p 0 (fun _=>x):=by have ht:= Zeph.Dew.Railing x p 0 (by rw[zero_smul]; exact H) i; rw [zero_smul] at ht; exact ht
        unfold jet;rw [← hx,norm_mul]; apply le_trans _ hv; exact mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_inv,Real.norm_natCast]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr i.factorial_pos))
lemma billH (hp: ContDiffAt ℝ ω p 0)(h:Past p x k a u)(hi:i+1≤ k)(hz:0<Z)(ha:0≤a)(hu:0≤u): ‖p (Z • x)- ∑ j∈range (i+1), Z^j*jet p j x‖ ≤ a^(i+1)*u*Z^(i+1):=by
       let g(t:ℝ):=p (t • x); have he:ContDiff ℝ ∞ g:=h.1
       have hx(v:ℕ): WardBin.leading v g=jet p v x:=by unfold jet WardBin.leading; have ht:= Zeph.Dew.Railing x p 0 (by rw[zero_smul]; exact hp) v; rw [zero_smul] at ht; rw [show iteratedDeriv v g 0=iteratedFDeriv ℝ v p 0 (fun _=>x) from ht]; rfl
       simp_rw[←hx]; exact Spells.paceT g Z hz i (he.of_le (WithTop.coe_le_coe.mpr le_top)) _ (mul_nonneg (pow_nonneg ha _) hu) (fun t _=> h.2 _ (Nat.succ_pos _) hi _)
end
end YM.OPE.Merchant.Aloof
