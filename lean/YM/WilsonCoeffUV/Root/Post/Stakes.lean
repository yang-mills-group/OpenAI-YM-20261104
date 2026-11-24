import YM.WilsonCoeffUV.Root.Post.Receipt
/-!
# Header input price. Includes marks not necessarily in a unit column.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {P:Patch}{n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}
variable {I:Bulb G}

structure Stakes (Y:Single G D) : Prop where
   pur :∀ i,Pure (Y i)
   vert: vertical Y
   m:∀ i j,mural (Y i j)
lemma Stakes.sub {Y X:Single G D}(y:Stakes Y)(x:Stakes X):Stakes (Y-X):=by
    refine ⟨fun i j p v=> congr_arg₂ (·-·) (y.pur i j p v) (x.pur i j p v), vertical_pair y.vert x.vert,?_⟩
    intro i j f a b; change Y i j _ - X i j _= _; rw [y.m i j f a b,x.m i j f a b,← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i hi=> (smul_sub ..).symm
-- export tariff uniform ∃ with positivity
lemma paid_echo (F:Frame G h)(s:ℝ)(p:0<s)(r D): ∃ C:ℝ,0≤C∧∀ i:Alma F,∀Y:ChamberTen G (Vote D) r,∀ B:ℝ,Twig 0 s B Y → ‖echoS F Y i‖≤C*B:=by
   let f (i):= ‖Bell F (weave F i) (valence F i)‖*plaud G h s r (valence F i)*‖brow F i D‖; let V:= ∑ i,|f i|; refine ⟨V,by unfold V; positivity,fun i Y B v=>?_⟩
   exact (echo_cost F Y i v p).trans (le_trans (le_of_eq (show _= f i *B by unfold f; ring)) (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum (f:=(fun i=>|f i|)) (fun _ _=> abs_nonneg _) (Finset.mem_univ _))) v.1))
lemma echo_add {P Q:ChamberTen G (Vote D) r}(i:Alma F)(v:Twig 0 s A P)(u:Twig 0 t B Q)(p:0<s)(q:0<t): echoS F (P+Q) i=echoS F P i+echoS F Q i:=by unfold echoS trellis; rw [arret_add _ _ _ v u p q,map_add]; rfl
lemma lower_lease (F:Frame G h)(r D e:ℕ)(s:ℝ)(hp:0<s): ∃ C:ℝ,0≤C ∧∀ Y:Single G D, Stakes Y→∀ A:ℝ,0≤ A→ (∀ i< e,∀ j,Twig 0 s A (Y i j))→(∀ i:Alma F,valence F i=r → ‖glean F Y e i‖≤ A) → Hears F h (C*A) (Y e r)∧ Wing 0 s (C*A) (Y e r):=by
   choose T ht hx using fun r=>paid_echo F s hp r D
   let K:=1+∑ i∈Finset.range r,T i; let V:=levyWind G s e (r-1)
   have hK:0≤ K:= add_nonneg zero_le_one (Finset.sum_nonneg fun i _=>ht _); have hv:0≤ V:= levyWind_nn ..
   refine ⟨K+V,by positivity,fun Y g A h q p=>?_⟩; have hg :0≤(K+V)*A:=by positivity
   constructor
   · refine ⟨hg,fun i _ z=>?_⟩
     have he:= p i z; rw [tail_glint,z] at he
     let f (j:ℕ):= if r≤e+j then echoS F (Y (e+j-r) j) i else 0
     have hπ : echoS F (Y e r) i= ((∑ i∈Finset.range r,f i)+echoS F (Y e r) i)-(∑ i∈Finset.range r,f i):=by abel
     rw [hπ]; apply (norm_sub_le ..).trans; apply le_trans _ (b:=K*A) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hv) h); unfold K; rw [add_mul,one_mul]; apply add_le_add he; apply (norm_sum_le ..).trans; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun j hj=>?_; unfold f; have hi:= Finset.mem_range.mp hj; split; · exact hx j i _ A (q _ (by omega) _)
     rw [norm_zero]; exact mul_nonneg (ht _) h
   cases r with
   | zero=> exact hg
   | succ r=> exact Wing.cap (r:=r+1) (roar_le_levy g.vert g.pur (C:=A) (e:=e) (r:=r) (fun i hi j _=> q i hi j) hp.le h) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) h)

-- feed difference same polynomial cost via synchronized basis-independent matrices
lemma pulse_diff (P:Patch)(w:Site P.L)(q:Drip P G)(p:dragCup Bank.terrain s B q)(F F': ChamberTen G (Vote D) r)(hf: Twig 0 t A F)(hg:Twig 0 t A F')(hp:0<s)(ht:s/P.L.val ≤t): pulseS P w q (F-F')=pulseS P w q F-pulseS P w q F':=by
    let u:= featherS P w F; let v:= featherS P w F'
    have he (K:ChamberTen G (Vote D) r)(h: Twig 0 t A K) x:= pumpFaceReady ((Cork.turn (lift w) h).touch (soprano P w D)) (fun _:Fin r=>p) ht hp x
    unfold pulseS; rw [show featherS P w _ =u-v from funext fun x=> map_sub (soprano P w D) _ _]; ext1 x; rw [pump,Pi.sub_apply,pump,pump]; rw [← (show Summable (spinJob (featherS P w F) (owns P.L q) x) from he F hf x).tsum_sub (show Summable (spinJob (featherS P w F') (owns P.L q) x) from he F' hg x)]; exact tsum_congr fun i=> smul_sub ..
lemma hall_diff (P:Patch)(q:Drip P G)(p:dragCup Bank.terrain s B q)(F F':ChamberTen G (Vote D) r)(hf:Twig 0 t A F)(hg:Twig 0 t A F')(hp:0<s)(ht:s/P.L.val≤t)(h): hall P h q (F-F')=hall P h q F-hall P h q F':=by unfold hall; simp_rw [pulse_diff P _ _ p F F' hf hg hp ht,Finset.sum_sub_distrib,smul_sub]
lemma stride (L:Tand I k r D)(h:ℕ)(p: Twig 0 I.input C (L.Z k r)): Twig 0 I.exitS (((I.path.patch.L.val:ℝ)^h *((r+1:ℕ)*I.path.D^r*Real.exp (8*I.s)*tiePay (Pick I.path) r (I.s-I.exitS)))*C*L.σ) (hall I.path.patch h L.P.P.Q (L.Z k r)- hall I.path.patch h L.P.Q.Q (L.Z k r)):=by
   let Y:= L.Z k r; let M:=I.path.patch; let V:= I.path.D; let s:= I.s; let t:= I.exitS
   let A:= tiePay (Pick I.path) r (s-t); let K:=(r+1:ℕ)*V^r*(C*Real.exp (8*s))*A
   have hv (w:Site M.L): Shelf Bank.terrain 0 t K L.σ (pulseS M w L.P.P.Q Y) (pulseS M w L.P.Q.Q Y):=by
       have he:= ((pays_feather _ w (Shelf.encore p L.P.θ)).portal I.ports (I.positive.trans I.vio).le)
       let T:= gatherT _ w (lift w) L.Z k
       unfold pulseS; rw [inspectFace,inspectFace]; exact Shelf.prismLens (P:=tiles M.L T) (Q:=tiles M.L T) he (L.P.Υ.mono (I.outlet.trans I.path.holds.le)) I.vio I.positive.le
   have ht:= (Shelf.sum (S:=Finset.univ) (fun w _=>hv w)).μ (tiara M h); rw [tier_cash] at ht; apply ht.toll.cost; exact le_of_eq (by unfold K A M V s t; ring)
end YM.WilsonCoeffUV.Cosmos
