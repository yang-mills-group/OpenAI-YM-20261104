import YM.WilsonCoeffUV.Product.Report.ReturnBase
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Convergence powers on compatible finer cutoffs
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b b' v u m M N a:ℕ}{H:Hol G} {x δ Z y:ℝ} {E W V' W':Credit}{R:Realm G (e+1) E}
variable {c':ℕ}{Q:Fin (a+1)→SealR G}
variable {F:Frame G h}{T:SectionData F}{p:h<D}{w:Rails h k u e}{K V' W':Credit}
lemma chargeTrans (S:Schedule)(m b c:ℕ)(v:b≤ m): trailC S m c ≤ paceT S m b * trailC S b c:=by
   unfold trailC; rw [pace_rep,← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith [scales S v]
lemma yieldRetarget [NormedAddCommGroup U]{S T:Ten U (Cloth α) r}{o η}(q:YieldP o η u A δ S T)(z:1 ≤ B)(v:δ ≤ B*x): YieldP o η u (B*A) x S T:=by rw [mul_comm B]; refine ⟨q.wax.more (le_mul_of_one_le_right q.nn z),q.wane.more (le_mul_of_one_le_right q.nn z),?_⟩; rw [mul_assoc]; exact q.toll.more (mul_le_mul_of_nonneg_left v q.nn)
lemma tallPair (H:Hol G)(Q:Fin (a+1)→ SealR G)(T:SectionData F)(p:h<D)
    (w: Rails h k u e)(g:capP Q≤k)(E W U V B L:Credit)
    : ∃ C:Credit,
    ∀ (Y:Torch H T p w E W U) (P:ChorusLine H T p e E W V),P.arch=Y.L→ let R:=Y.L.V;
    HorizonP H R W V Q→ SpringD R (capP Q) u (capP Q+2) B→ Dormitory R (capP Q) u L→
    ∀ m b j N M c (F: Wilt Q)(X Y: Herit Q)(A B: Fin (a+1)→ℝ)(Z:ℝ),
    R.anchor ≤ j → j ≤ b → b≤ m → m≤c → c≤ N → c≤ M →
    Compar R.draws.S R.y j m ≤ Z →
    Bough Q F (paceT R.draws.S m b) Z B →
    Sitting Q A e (R.tempC m c) X Y →
   ∀ i≤ e,∀ l, let t := (∏ i,B i*A i); twain (C.buy Z*t) (R.tempC m c) (coeff i (Reports R.draws R.paid T p F X m b j N k l)) (coeff i (Reports R.draws R.paid T p F Y m b j M k l)):=by
    obtain ⟨S,hS⟩:= importation H Q E W V B L e u D; obtain ⟨C,hC⟩:= CutsP.stature H T p w E W U V; obtain ⟨V',hV⟩:= agesQuote H T p e E W V
    let X:=((Credit.leanC.powC h).prodC ((V'.prodC C).prodC (Credit.leanC.prodC S)))
    refine ⟨X,?_⟩; intro Y P' u' R H' p' v m b j N M c F' P Q' A B' Z hj hb hb' hc hn hM hz hGG x i l y t
    let K:=R.draws.S; let V'' := Compar K R.y j m; have hQ:= PadRank.frugal R hj (hb.trans hb'); have hZ: PadRank R b m Z:=by let f:=hQ.zone hb (le_refl m); exact ⟨fun _ i v=>(f.year _ i v).trans hz, f.lengthS.trans hz⟩
    let θ:= R.tempC m c; have hv:0≤θ:= (trail_pos ..).le; let J:= paceT K m b; have hh':J≤Z:= (le_abs_self J).trans hGG.room; have hJ:0≤ J:= (pace_pos ..).le
    have hX:θ≤ Z*R.tempC b c:= (chargeTrans K m b c hb').trans (mul_le_mul_of_nonneg_right hh' (trail_pos ..).le)
    let A' n σ:= AutumnDay R.draws R.paid F' σ m b n D; let G':= (Credit.leanC.prodC S).buy Z*t; have he : 0≤t:= Finset.prod_nonneg fun i _=> mul_nonneg (hGG.lanes i).1 (x.stock i); have hB:0≤ G':=mul_nonneg (zero_le_one.trans (Credit.purchase _ hGG.pos)) he
    have hey:= hS R H' p' v m b c N M F' P Q' A B' Z θ (hj.trans hb) hb' hc hn hM hZ hGG le_rfl x
    have hy' : j+(b-j)=b:=by omega
    let Q0 :CutsP H T p w E W U V:= ⟨Y,P',u',j,b-j,c,N,M,hj,(by omega),hn,hM,A' N P,A' M Q',GatesC H' F' P (hj.trans hb) hb' (hc.trans hn) g, GatesC H' F' Q' (hj.trans hb) hb' (hc.trans hM) g,G',hB,fun l i v=>by
      rw [hy',show G'= Z * (S.buy Z *t) from by unfold G'; rw [Credit.products,Credit.lean_cost, mul_assoc]]; exact yieldRetarget (hey l v i) hGG.pos hX⟩
    let VQ n s:=tallyV R.draws R.paid T p n k b j (A' n s)
    have hτ : Q0.δm≤θ:=by change R.tempC (j+(b-j)) c≤θ; rw [hy']; exact PathCost.narrow K hb' _
    have hu : Q0.Age≤ Z:=by unfold CutsP.Age WindowS.Age CutsP.windowC; dsimp only [Q0, CutsP.vesselsC]; rw [hy']; exact ((compar_age K R.y j) hb').trans hz
    have hbN : Q0.tileP=VQ N P := by unfold CutsP.tileP CutsP.ceilC Q0; dsimp only [CutsP.ax,CutsP.tx,CutsP.vesselsC]; rw [hy']
    have hbM : Q0.tileQ=VQ M Q' := by unfold CutsP.tileQ CutsP.ceilC Q0; dsimp only [CutsP.ax,CutsP.tx,CutsP.vesselsC]; rw [hy']
    let B0:= C.buy Z * G'; have hP : 0≤ B0:= mul_nonneg (zero_le_one.trans (C.purchase hGG.pos)) hB
    have h' (i:ℕ) (l:i≤e) y: twain B0 θ (coeff i (VQ N P y)) (coeff i (VQ M Q' y)):=by rw [←hbN,←hbM]; exact ((hC Q0 i l y).wide hτ).lift (mul_le_mul_of_nonneg_right (C.elder Q0.windowC.warm hu) hB) hv
    let R':CourseS H T p e E W V:= ⟨P',⟨R,b,m-b,N,M,c,hj.trans hb,(by omega),hn,hM⟩,by change R=P'.arch.V; rw [u']⟩
    have hR:b+(m-b)=m:=by omega
    have hT:Compar K R.y b m≤ V'':=by
       unfold V'' Compar; have hp: R.y b ≤ R.y j +(K.scale b-K.scale j):= R.age j b hj hb; have h : (↑(m-b):ℝ)≤ ↑(m-j):=by exact_mod_cast (show m-b≤m-j by omega)
       linarith only [hp,h]
    have H0:R'.cab = θ:=by unfold CourseS.cab WindowS.cab R'; dsimp only; rw [hR]
    have H1:R'.Age ≤ Z:=by unfold CourseS.Age WindowS.Age R'; dsimp only; rw [hR]; exact hT.trans hz
    have HH:= hV R' (VQ N P) (VQ M Q') B0 θ hP H0.le h' i l y
    let C0:= V'.buy Z* B0; let VQ' n s:=steep R.draws R.paid T p n b (m-b) s
    have hy'':twain C0 θ (coeff i (VQ' N (VQ N P) y)) (coeff i (VQ' M (VQ M Q') y)):=by
          apply twain.lift _ (mul_le_mul_of_nonneg_right (V'.elder R'.I.warm H1) hP) hv; have ht:R'.vols=R:= by change P'.arch.V=R; rw [u']
          dsimp only at HH; rw [ht] at HH; exact HH
    have HN:m≤N:=hc.trans hn; have HM:m≤M:=hc.trans hM
    let ax:=VQ' N (VQ N P); let ux:= VQ' M (VQ M Q'); have hr:Reports R.draws R.paid T p F' P m b j N k=J^h • ax:= tall_report Y H' P F' hj hb hb' HN g; have hκ:Reports R.draws R.paid T p F' Q' m b j M k=J^h • ux:=tall_report Y H' Q' F' hj hb hb' HM g
    rw [hr,hκ,Pi.smul_apply,Pi.smul_apply,map_smul,map_smul]; apply twain.lift ⟨_,_,_⟩ (show J^h*C0 ≤ X.buy Z*t from ?_) hv
    · rw [norm_smul, Real.norm_eq_abs,abs_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left hy''.main (by positivity)
    · rw [norm_smul, Real.norm_eq_abs,abs_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left hy''.side (by positivity)
    · rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_assoc]; exact mul_le_mul_of_nonneg_left hy''.gap (by positivity)
    apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hJ hh' h) hy''.nn); unfold X C0 B0; rw [Credit.products]; rw [Credit.products,Credit.products,Credit.power,Credit.lean_cost]; exact le_of_eq (by ring)
end YM.WilsonCoeffUV.Mer
