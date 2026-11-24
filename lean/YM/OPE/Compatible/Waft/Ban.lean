import YM.OPE.Compatible.Waft.Lid
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
namespace PriceZ
variable {W L: Type}
variable {K:Sponsor G}{T: Seasons K}{v:W→ℝ}{P:ChartRatio G}
variable (A:(i':W)→Alps K T i (v i'))(X:W→Side)(H:∀ i,Even (X i).val)(V:∀ i,Plot (H i))
local notation "Y" j=>Libra.Keys G (Stand.Free (V j))
def kBill (P:ChartRatio G): ℝ:=‖iteratedFDeriv ℝ 2 (rake P) 0‖
lemma T_normX (y:G.Color):‖jet (rake P) 2 y‖≤ kBill P*‖y‖^2:=by
    rw [njet, norm_div]; let T:=iteratedFDeriv ℝ 2 (rake P) 0; have hp:= T.le_opNorm ![y,y]; apply le_trans (div_le_self (norm_nonneg _) (by norm_num)); apply hp.trans_eq; simp [kBill,pow_succ,T,Fin.prod_univ_succ]
lemma payJ (U: ChartRatio G)(h:LocalRatio U)(z:W)(x:Y z): jet (looper U) 2 x=∑ i:(V z).Free, jet (rake U) 2 (x i):=by
    unfold looper jet; rw [iteratedFDeriv_fun_sum_apply (f:=fun i:(V z).Free=>fun p:Libra.Keys G (V z).Free=> Real.log (U.J (p i))) (u:=Finset.univ) (fun i _=>?_),_root_.sum_apply]; rw [mul_sum]; apply sum_congr rfl; intro i _; apply congr_arg; let f: (Y z)→L[ℝ] G.Color:= ContinuousLinearMap.proj i; change (iteratedFDeriv ℝ 2 (rake U ∘ f) 0) _=_; rw [jets_linear f ((jet_trunk h).1.of_le le_top)]; rfl
    exact (((show ContDiffAt ℝ ω (rake U) ((ContinuousLinearMap.proj i: (Y z)→L[ℝ] G.Color) 0) from (jet_trunk h).1).comp 0 (ContinuousLinearMap.proj i: (Y z)→L[ℝ] G.Color).contDiff.contDiffAt)|>.of_le le_top)
lemma PayJ' (U:ChartRatio G)(h:LocalRatio U): WindZ X 4 2 1 fun j x=> jet (looper U) 2 (x:Y j):=by
     let b:= kBill U; have hb:0 ≤ b:=norm_nonneg _; refine ⟨⟨4*b,by positivity,fun i x=>?_⟩,fun i=> bondJets (fun y:Y i=>y) _ _ (fun f=> Bond.glyph f)⟩
     rw [payJ]; swap; · exact h
     apply (norm_sum_le ..).trans; apply (Finset.sum_le_sum (g:=fun (_:(V i).Free)=> b*(1+‖x‖)^2) (fun j _=>?_)).trans; swap; · apply (T_normX _).trans;gcongr; exact (norm_le_pi_norm x _).trans (le_add_of_nonneg_left zero_le_one)
     have hs : Fintype.card ((V i).Free)≤ (X i).val^4 *4:=by
          apply le_trans (Fintype.card_le_of_injective (fun p:(V i).Free=> (p.val: Limb (H i))) Subtype.val_injective) ((Fintype.card_le_of_injective (fun p: Limb (H i)=> p.val) Subtype.val_injective)|>.trans ?_); change Fintype.card (Site (X i) × Axis) ≤ _; rw [Fintype.card_prod,site_card]; rfl
     rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; let v:=((X i).val:ℝ); apply le_trans (mul_le_mul_of_nonneg_right (show ↑(Fintype.card ((V i).Free))≤ v^4*4 from (by unfold v; exact_mod_cast hs)) (by positivity)); unfold care; rw [Pi.one_apply,mul_one]; unfold b v; apply le_of_eq; ring
abbrev PathL (B:ℝ)(g:W→ℝ):Prop:= ∀ i,|g i|≤B
lemma saleV {b:ℝ} {g:W→ℝ}(hv:PathL b g):Cash X 0 1 g:= ⟨max 0 b,le_max_left ..,fun i=>by rw [pow_zero,Pi.one_apply,mul_one,mul_one]; exact (hv i).trans (le_max_right ..)⟩
-- α.Γ
lemma BootPrice {p:Clip}(U:ChartRatio G)(ht:LocalRatio U)(B C:ℝ)(g:W→ℝ)(V':∀ i,Bor (H i) (A i) (g i))(h:PathL B g)(hc:0≤v)(hc':∀ i,v i≤C)(hz:0 ≤ C)(hp:∀ i,(A i).clip=p)(hs:G.Simple): WindT X 8 6 1 fun i=> ( Bor.L (V' i) (V i)).hat U:=by
      let f(j:ℕ)(i:W)(x:Y i):= jet (swornV (A i).clip (A i).live) j (rayS _ (V i) G x)
      let w(i:W)(x:Y i):= jet (swornY (A i).live) 2 (rayS _ (V i) G x); let K(i:W)(x:Y i):= jet (looper U) 2 x; let t:=(-(4:ℝ)⁻¹) • f 3; let u(i:W):=g i • ( (-(4:ℝ)⁻¹) • f 2 i); let r:=((-(4:ℝ)⁻¹) • f 4)+ u + (-(4:ℝ)⁻¹) • w + K; have hf(kind):WindZ X 4 kind 1 (f kind):=pegV _ _ _ _ hp kind; have hv(i:W)(x:Y i):( Bor.L (V' i) (V i)).hat U x=flareTok (t i x) (r i x):=by
          rw [SwiftD (H i) (V i) (V' i) ht hs]; dsimp only; rw [receipt (H i) (V i) (V' i), ←penon_shape, cargo _ _ _ _ _ (by decide)]; unfold t r u f w K; simp only [Pi.add_apply, Pi.smul_apply,smul_eq_mul]; ring_nf
      have hx: WindZ X 4 3 1 t:= (hf 3).smul _; have hg: Cash X 0 1 g:=saleV X h; have hU: WindZ X 4 2 1 u:=by simpa only  [u, Pi.smul_apply,one_mul,zero_add] using (WindZ.scale ((hf 2).smul (- (4:ℝ)⁻¹)) hg zero_le_one)
      have hr: WindZ X 4 4 1 r:= ((((hf 4).smul _).add (hU.gauge zero_le_one le_rfl le_rfl (by omega))).add ((WindZ.smul (show WindZ X 4 2 1 w from pegW A X H V 2 C hc' hz hc) _).gauge zero_le_one le_rfl le_rfl (by omega)) |>.add ((PayJ' X H V U ht).gauge zero_le_one le_rfl le_rfl (by omega)))
      intro j; simp_rw [hv]; fin_cases j; exact WindZ.unit ..; exact hx.gauge zero_le_one le_rfl (by omega) (by omega)
      have hs: WindZ X 8 6 1 (t*t):=by simpa only [mul_one] using (hx.mul hx zero_le_one)
      have hZ:= (hr.gauge zero_le_one le_rfl (show 4≤8 by decide) (show 4≤6 by decide)).add (hs.smul (2:ℝ)⁻¹); convert hZ using 1; funext i x; change r i x+(t i x)^2/2=r i x+_; simp only [Pi.smul_apply,smul_eq_mul,Pi.mul_apply]; ring
end PriceZ
end YM.OPE.Quit
