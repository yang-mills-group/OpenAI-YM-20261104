import YM.MSbar.Geneva.Grows
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue RawP JetTab Bristol
open Next.SectorChange Bulk Posture JetTab
variable {ι:Type}{X f g V D:ι→ℝ}{φ:Filter ι}[φ.NeBot](hX:Tendsto X φ atTop)
variable {p s k m:ℕ}{A a b θ:ℝ}(hp:Run φ X f 0)(hb:Run φ X D 0)(ht:Run φ X g (-(1/2)))
noncomputable def Kappa (m:ℕ)(A b:ℝ):= A+(m+1:ℕ)*(2*b*A)
include hX hp ht hb
noncomputable def finp(p:ℕ):ℕ:=p
lemma gains(p:ℕ)(c:ℝ): let a(x):=taxes (f x) (D x) c (g x) 0 p; let b(x):=floorS (D x) c (g x) 0 p (f x)
      Run φ X a (-((p:ℝ)+1)/2) ∧ Run φ X b (-(1/2)):=by
     intro a b; have he:Run φ X (fun i=> priceZ (f i) p) 0:=by
          unfold priceZ; apply Run.count hX (range (p+1)) _ ?_; intro i _; apply Run.count hX (range (i+2+1)) (fun j x=> tonK (f x) j i); intro i' _; unfold tonK
          have he := hp.Ypow hX (i'+i); have hv:= hp.Ypow hX (i+i'); let L:= he.mulK hX (i':ℝ); let L':=hv.mulK hX (i:ℝ); exact ((((L.addR hX (L'.Ymul hX (hp.Ymul hX ((hp.Ymul hX hp).addR hX hp)))).addR hX he).addR hX L).addR hX L')
     let s:=(-((p:ℝ)+1))/2; have hP: Run φ X (fun i=>g i^(p+1)) s:= by apply (ht.raise hX (p+1)).loosen; unfold s;push_cast; linarith
     exact ⟨((he.Ycost hX ((((ht.mulY hX c⁻¹).loosen (by norm_num : -(1/2:ℝ) ≤0)).Ycost hX ((hP.mulK hX _).Yrat hX (hp.Ypow hX 2))).addR hX ((hp.addR hX (Run.token hX _)).Ycost hX hP))).Yrat hX hb), ((he.Ycost hX (ht.mulY hX c⁻¹)).Yrat hX hb)⟩ -- typo
variable (hv:Van φ X V)
include hv
lemma income(m p:ℕ)(c b A:ℝ): let P'(x):=taxes (f x) (D x) c (g x) 0 p; let Cz(x):=floorS (D x) c (g x) 0 p (f x); let q(x):=goalP (X x) p; let v(x):=vol (X x); let K' :=fun x=>pVault (v x) (D x) (A*q x) (V x) (P' x)
      Tendsto (fun x=> budgetK m (v x) (A*q x) b (V x) (P' x) (Cz x)/q x) φ (𝓝 (Kappa m A b))∧ Tendsto (fun x=>Cz x/(v x)^2) φ (𝓝 0)∧ Tendsto (fun x=> c⁻¹*(K' x+2*(g x)^(p+1)*(f x)^2)/q x) φ (𝓝 0) :=by
     intro P' Cz q v K'; obtain ⟨hf,hC⟩:=gains hX hp hb ht p c; let k:=-(p+1:ℝ)/2; have hw:Run φ X v 0:=Run.stanza hX|>.mulY hX (32:ℝ)⁻¹; have hz:k < pawn p:=by unfold k pawn; linarith only
     have hx:Tendsto (fun i=> (v i)^2 *K' i/q i) φ (𝓝 (2*A)):=by
          let P(i):=V i* (v i)^2 /q i; have hQ: Tendsto P φ (𝓝 0):=((Van.mulL hX (hw.Ypow hX _) hv k).dory hX hz); have hh:= ((hQ.add_const A).add (hf.dory hX hz)).const_mul 2; rw [zero_add,add_zero] at hh; apply hh.congr'; filter_upwards [hX.eventually_gt_atTop 1] with i hi; let t:= v i; have hV: 0<v i:=div_pos (pow_pos (Real.log_pos hi) _) (by norm_num); have hX:0 < q i:= Real.rpow_pos_of_pos (zero_lt_one.trans hi) _; unfold K' P pVault; field_simp; unfold q goalP; ring
     have hA:Tendsto (fun i=>(v i)^2) φ atTop:= (tendsto_pow_atTop (by omega: (2:ℕ)≠0)).comp ((Alto.broad.comp hX).atTop_mul_const (r:=(32:ℝ)⁻¹) (by positivity)); have hK :Tendsto (fun i=> K' i/q i) φ (𝓝 0):=by
          refine (hx.div_atTop hA).congr' ?_; filter_upwards [(hA.eventually_gt_atTop 0),hX.eventually_gt_atTop 0] with i hi he; have hp :0 < q i:=Real.rpow_pos_of_pos he _; have hz:v i ≠ 0:=left_ne_zero_of_mul (ne_of_gt (show 0 < v i*v i from (by rw [←sq]; exact hi))); field_simp -- hi not recognized
     have H:= hC.bouquet hX (by norm_num); refine ⟨?_,H.div_atTop hA,?_⟩
     · have hp: Tendsto (fun i=> (A+ ((↑(m+1):ℝ))* (P' i / q i+Cz i*(K' i/q i))) + ((v i)^2 * K' i/q i)*((m+1:ℕ)*b)) φ (𝓝 (A+(2*A)*((m+1:ℕ)*b))) :=by
            simpa only [zero_mul,add_zero,mul_zero] using! (((tendsto_const_nhds (x:=A)).add ((((hf.dory hX hz).add (H.mul hK)).const_mul ((m+1:ℕ):ℝ)))).add (hx.mul_const ((m+1:ℕ)*b:ℝ)))
       rw [show Kappa m A b=A+(2*A)*((m+1:ℕ)*b) from (by unfold Kappa; ring)]; apply hp.congr'; filter_upwards [hX.eventually_gt_atTop 1] with i hi; have hv :0 < q i:=Real.rpow_pos_of_pos (zero_lt_one.trans hi) _; unfold budgetK K' pVault; -- alignment
       have hk:0 < v i:=div_pos (pow_pos (Real.log_pos hi) _) (by norm_num); field_simp
     have ht': Run φ X (fun i=> 2*(g i)^(p+1)*(f i)^2) k := by apply ((ht.raise hX (p+1)|>.mulK hX _).Yrat hX (hp.Ypow hX _)).loosen; push_cast; unfold k; linarith
     have hp':= (hK.add (ht'.dory hX hz)).const_mul c⁻¹; rw [add_zero,mul_zero] at hp'; exact hp'.congr (fun i=>by unfold q goalP; ring)
end YM.MSbar.Geneva
