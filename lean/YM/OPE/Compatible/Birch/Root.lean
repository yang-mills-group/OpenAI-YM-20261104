import YM.OPE.Compatible.Birch.Teasel
/-! Monetary algebra edges. Includes changing kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {I J W:Type*} {i j n r d m:ℕ}{G:Gauge}{s b U D t ε:ℝ}{N:Side}
namespace Script
open Page
-- combine δ Data. norm C ballot
lemma tallyProd {f g c:Fin r→ℝ}(hx:∀ i,‖f i‖≤c i)(hg:∀ i,‖g i‖ ≤ c i)(ht:∀ i, ‖f i-g i‖≤ ε*c i)(h:0 ≤ ε): ‖(∏ i,f i)-(∏ i,g i)‖≤ (r:ℝ)*ε*∏ i,c i:=by
    induction r with
    | zero=>simp
    | succ r ih=>
       let v(i:Fin r):= f i.succ;let u(i:Fin r):=g i.succ; let w(i:Fin r):= c i.succ; let x:=∏ i,v i;let y:=∏ i,u i;let B:=∏ i,w i; have hy:0≤B:= prod_nonneg fun i _=> (norm_nonneg _).trans (hx _)
       have hp: ‖y‖≤B:=by unfold y;rw [norm_prod]; exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>hg _)
       have he: 0≤c 0:=(norm_nonneg _).trans (hx _); have hz: ‖x-y‖≤ (r:ℝ)*ε*B:= ih (fun i=>hx i.succ) (fun i=> hg i.succ) (fun i=>ht i.succ)
       rw [Fin.prod_univ_succ,Fin.prod_univ_succ,Fin.prod_univ_succ]; change ‖f 0*x-g 0*y‖≤ _*ε*(c 0* B); rw [show f 0*x-g 0*y=f 0*(x-y)+(f 0-g 0)*y by ring]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; apply (add_le_add (mul_le_mul (hx 0) hz (by positivity) he) (mul_le_mul (ht 0) hp (norm_nonneg _) (mul_nonneg h he))).trans; exact le_of_eq (by push_cast; ring)
abbrev absW (A:Row I J):Row I J:= fun i j k=>‖A i j k‖
lemma absWstrip {A:Row I J}(h:A.strip s D): (absW A).strip s D:=fun i j=> by simpa [absW,Width] using h i j
variable {A B:Cross N I J}
-- actor
lemma one_shunt (h:A.strip s U)(g:B.strip s U)(hp:(A-B).strip s (ε*U))(hh:0<ε):
   let T:=plusRows (plusRows (absW A) (absW B)) (scaleRows ε⁻¹ (absW (A-B)))
   T.strip s (U+U+U) ∧ ∀ p i,‖linePay A p i‖≤ linePay T p i∧‖linePay B p i‖ ≤ linePay T p i ∧ ‖linePay A p i-linePay B p i‖≤ ε*linePay T p i:=by
     intro T; refine ⟨?_,fun p i=> ?_⟩
     · exact (show (U+U+‖ε⁻¹‖* (ε*U))= U+U+U by rw [Real.norm_of_nonneg (inv_nonneg.mpr hh.le),inv_mul_cancel_left₀ hh.ne']) ▸ FreeResolvent.strip_plus (FreeResolvent.strip_plus (absWstrip h) (absWstrip g)) (strip_scale (absWstrip hp) _)
     let a:=linePay A p i;let b:=linePay B p i; let c:=linePay T p i; change ‖a‖≤ c ∧ ‖b‖≤ c ∧ ‖a-b‖ ≤ ε*c; have hc : c= ‖a‖+‖b‖+ε⁻¹*‖a-b‖:=by simp [T,c,plusRows,minusRows,scaleRows,absW,a,b,linePay]
     rw [hc]; constructor; exact (le_add_of_nonneg_right (norm_nonneg _)).trans (le_add_of_nonneg_right (by positivity)); constructor; exact (le_add_of_nonneg_left (norm_nonneg _)).trans (le_add_of_nonneg_right (by positivity));rw [mul_add,mul_inv_cancel_left₀ hh.ne']; exact le_add_of_nonneg_left (by positivity)
lemma rakeChange [Fintype J](h:A.strip s U)(g:B.strip s U)(hp:(A-B).strip s (ε*U))(hh:0<ε)(hs:0<s){p:Script I r}(w:Cover)(hc:soot m p D):
   soot m (countermove A w p-countermove B w p) ((r:ℝ)*ε*(D*regionB J s (U+U+U) (size w) r m)):=by
    let T:=plusRows (plusRows (absW A) (absW B)) (scaleRows ε⁻¹ (absW (A-B))); obtain ⟨hT,ha⟩:= one_shunt h g hp hh
    have he:= cashmoves hT hs p w hc; have hA:= cashmoves h hs p w hc; have hB:=cashmoves g hs p w hc
    let f(X:Cross N I J)(i:Page I r)(j:Page J r):= p i* call X w i j; let x:ℝ:= r*ε; have hx:0 ≤ x:=by unfold x; positivity
    have hu(i:Page I r)(j:Page J r): ‖call A w i j - call B w i j‖≤ x*‖call T w i j‖:=by
       have ht:= tallyProd (r:=r) (c:=fun t=>linePay T (Page.slide w i t) (j t)) (fun t=>(ha _ _).1) (fun t=>(ha _ _).2.1) (fun t=>(ha _ _).2.2) hh.le; exact ht.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hx)
    let q(i: Page I r)(j:Page J r):= f A i j-f B i j; have hz:Sack (fun i:Page I r × Page J r=> figure m i.2) (uncurry q) (x*(D*regionB J s (U+U+U) (size w) r m)):=by
       let u(i:Page I r × Page J r):=figure m i.2*‖f T i.1 i.2‖; apply budget_minor (g:=fun i=> x*u i) _ (fun i=>mul_nonneg (zero_le_one.trans (payer m _)) (norm_nonneg _)); swap
       · refine ⟨fun i=>mul_nonneg hx (he.1 _), (show Summable u from he.2.1).mul_left _,?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he.2.2 hx
       intro i; unfold u; change figure m i.2 * ‖p i.1*_ - p i.1*_‖≤ _;rw [← mul_sub,norm_mul]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hu i.1 i.2) (norm_nonneg _)) (zero_le_one.trans (payer m _))).trans_eq; unfold f; rw [norm_mul]; ring
    rw [show countermove A w p-countermove B w p=(fun i=> ∑' j, q j i) from funext (fun i=> ((hA.collectible (payer m) i).of_norm.tsum_sub ((hB.collectible (payer m) i).of_norm)).symm)]; exact hz.draw (payer m)
end Script
end YM.OPE.Flume
