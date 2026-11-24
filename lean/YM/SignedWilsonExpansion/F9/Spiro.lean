import YM.SignedWilsonExpansion.F9.Cove
import YM.XSpace.FPS
/-!
# Complexification on slips and bookkeeping. Keep common orientation/time schedule.
-/
set_option autoImplicit false
set_option maxHeartbeats 690000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace FPS
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r p u n :ℕ}
variable {B Q D Z X Y η t a ρ d:ℝ}{E W U V:Credit}
variable {R:Realm G (e+1) E}{z:Cost}
abbrev InkQ:= PowerSeries ℂ
variable {x y:InkQ}
abbrev insertQ:Cost→+* InkQ:= PowerSeries.map (Complex.ofRealHom)
lemma inked (z:Cost) (i:ℕ): coeff i (insertQ z)=((coeff i z:ℝ):ℂ):=by rw [insertQ,coeff_map]; rfl
-- basic operators ring clock
abbrev aimS (p:InkQ)(H:constantCoeff p=0) : InkQ→ₐ[ℂ]InkQ:= substAlgHom (HasSubst.of_constantCoeff_zero' H)
lemma aimSh (p:InkQ)(x:InkQ)(H:constantCoeff p=0): aimS p H x= x.subst p:=congr_fun (coe_substAlgHom _) x -- types

noncomputable abbrev flyQ (p:Cost):InkQ→ₐ[ℂ]InkQ:= aimS (insertQ p*PowerSeries.X) (by simp)
lemma flyh (p x:Cost): flyQ p (insertQ x)= insertQ (Bank.reel p x) := by rw [flyQ,aimSh, Bank.reel_apply, FPS.substitute_ringHom _ _ (by simp)]; congr 1; rw [map_mul,map_X]
lemma flightX (p:Cost) : flyQ p PowerSeries.X=insertQ (p*PowerSeries.X):=by nth_rw 1 [← show insertQ PowerSeries.X= _ from map_X Complex.ofRealHom]; rw [flyh, reel_X]
noncomputable abbrev southQ (A:Levels G)(Ñ:ChartRatio G)(N m c:ℕ):InkQ→ₐ[ℂ]InkQ:= flyQ (relativeF A Ñ N m (c-m))
noncomputable abbrev northQ (A:Levels G)(Ñ:ChartRatio G)(N m c:ℕ):InkQ→ₐ[ℂ]InkQ:= flyQ (relativeC A Ñ N m (c-m))
lemma south_both (h:m≤c)(g:G.Simple)(p:LocalRatio Ñ)(v:c≤N)(y:InkQ) : southQ A Ñ N m c (northQ A Ñ N m c y)=y ∧ northQ A Ñ N m c (southQ A Ñ N m c y)=y:=by
    let X':InkQ:=PowerSeries.X; let F:=southQ A Ñ N m c; let V:=northQ A Ñ N m c; let a:Cost:=relativeF A Ñ N m (c-m); let b:= relativeC A Ñ N m (c-m)
    have he (a b:Cost)(v:chartB a b=1) : flyQ b (flyQ a y)=y:=by
       let X:=PowerSeries.X (R:=ℝ); have hx:flyQ b (insertQ a*X')=X':=by
           unfold X'; rw [← show insertQ PowerSeries.X= _ from map_X Complex.ofRealHom, ←map_mul, flyh, ←hit_chart, v,one_mul]
       have hV(s:Cost): constantCoeff (insertQ s*X')=0:=by simp only [X',map_mul,constantCoeff_X,mul_zero]
       have ha: HasSubst (S:=ℂ) (insertQ a*X'):= HasSubst.of_constantCoeff_zero' (hV a); have hu: HasSubst (S:=ℂ) (insertQ b*X'):= HasSubst.of_constantCoeff_zero' (hV b); simp_rw [flyQ,aimSh] at hx ⊢; rw [subst_comp_subst_apply ha hu,hx,X_subst]
    obtain ⟨h1,h2⟩:= direction (A:=A) g p (show m+(c-m) ≤ N by omega); exact ⟨he b a h2,he a b h1⟩

abbrev FitsZ (e:ℕ)(z:InkQ)(B:ℝ): Prop:=∀ i≤e,‖coeff i z‖≤B
namespace FitsZ
lemma written (f:FitS e z B): FitsZ e (insertQ z) B:=fun i v=>by rw [inked, Complex.norm_real]; exact f i v
lemma realX (f:FitsZ e (insertQ z) B): FitS e z B:= fun i v=> by rw [←Complex.norm_real, ←inked]; exact f i v
lemma nonneg (p:FitsZ e x B):0≤B:= (norm_nonneg _).trans (p 0 (Nat.zero_le _))
lemma lift (f:FitsZ e x B)(h:B≤Z):FitsZ e x Z:=fun i v=> (f i v).trans h
lemma plus (f:FitsZ e x B)(g:FitsZ e y D):FitsZ e (x+y) (B+D):= fun i v=> by rw [map_add]; exact (norm_add_le ..).trans (add_le_add (f i v) (g i v))
lemma minus (f:FitsZ e x B)(g:FitsZ e y D):FitsZ e (x-y) (B+D):= fun i v=> by rw [map_sub]; exact (norm_sub_le ..).trans (add_le_add (f i v) (g i v))
lemma neg (f:FitsZ e x B):FitsZ e (-x) B:= by intro i v; rw [map_neg,norm_neg];exact f i v
lemma mul (f:FitsZ e x B)(g:FitsZ e y D):FitsZ e (x*y) ((e+1:ℕ)*(B*D)):=by
   intro i h; rw [coeff_mul]; let S:= Finset.antidiagonal i; refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun _=> B*D) (s:=S) fun j hj=> ?_) ?_)
   · have hv:= Finset.mem_antidiagonal.mp hj; rw [norm_mul]; exact mul_le_mul (f j.1 (by omega)) (g j.2 (by omega)) (norm_nonneg _) f.nonneg
   rw [Finset.sum_const,nsmul_eq_mul,Finset.Nat.card_antidiagonal]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) (mul_nonneg f.nonneg g.nonneg)
lemma stack (S:Finset J)(P:J→InkQ)(V:J→ℝ)(f:∀ i∈S,FitsZ e (P i) (V i)):FitsZ e (∑ i∈ S,P i) (∑ i∈ S,V i):=by
   intro i h; rw [map_sum]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun j hj=> f j hj i h)
lemma oneZ : FitsZ e 1 1:=by intro i _; rw [coeff_one]; split <;> simp
lemma cum (S:Finset J)(P:J→InkQ)(V:J→ℝ)(f:∀ i∈S,FitsZ e (P i) (V i)): FitsZ e (∏ i∈S,P i) ((((e+1:ℕ):ℝ)^S.card)*(∏ i∈ S,V i)):=by
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.prod_empty, Finset.card_empty,pow_zero,mul_one]; exact oneZ
   | @insert i S h ih=> rw [Finset.prod_insert h,Finset.prod_insert h,Finset.card_insert_of_notMem h]; exact ((f i (Finset.mem_insert_self ..)).mul (ih (fun j hj=> f j (Finset.mem_insert_of_mem hj)))).lift (le_of_eq (by ring))
lemma pow (f:FitsZ e x B)(i:ℕ) : FitsZ e (x^i) ((((e+1:ℕ):ℝ)*B)^i):=by
   induction i with
   | zero=> simp only [pow_zero]; exact oneZ
   | succ i ih=> rw [pow_succ,pow_succ]; exact (ih.mul f).lift (le_of_eq (by ring))
lemma ticket (x:ℂ): FitsZ e (PowerSeries.C x) ‖x‖ := by intro i v; rw [coeff_C]; split; exact le_rfl; simp
lemma price_div (f:FitsZ e x B)(c:ℂ):FitsZ e (c • x) (‖c‖*B):=fun i v=>by rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (f i v) (norm_nonneg _)
lemma retape (p:FitsZ e x B) (q:FitsZ e y Z) (hx:1≤B)(h:constantCoeff x=0): FitsZ e (aimS x h y) ((e+1:ℕ)*(Z*(((e+1:ℕ):ℝ)*B)^e)):=by
    intro i h'; rw [aimSh,FPS.coeff_substituted y h]; let S:=Finset.range (i+1); let Q:=Z*(((e+1:ℕ):ℝ)*B)^e
    refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun _=> Q) (s:=S) fun j hj=> ?_) ?_)
    · have v:= Finset.mem_range.mp hj; let t:=(((e+1:ℕ):ℝ)*B); have hx:1≤t:= one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr (by omega)) hx
      rw [norm_smul]; exact mul_le_mul (q j (by omega)) (((p.pow j) i h').trans (pow_le_pow_right₀ hx (by omega))) (norm_nonneg _) q.nonneg
    rw [Finset.sum_const,nsmul_eq_mul,Finset.card_range]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) (by unfold Q; have hz:=q.nonneg; have he:0≤B:=p.nonneg; positivity)
-- direction credit Ω; T implementation `Bank.reel` is order-by-order; clocks are constant-on-epoch.
def hairC (G:Gauge)(e:ℕ)(E:Credit) : Credit:= let V:=Canopy.pageS G (e+1) E; let B:Credit:=⟨0,(e+1:ℕ),Nat.one_le_cast.mpr (by omega)⟩; (B.prodC ((B.prodC V).powC e))
lemma flight (g:Canopy R m c Z)(p:c≤ N)(u:FitsZ e x B): FitsZ e (southQ R.draws R.paid N m c x) ((hairC G e E).buy Z*B) ∧ FitsZ e (northQ R.draws R.paid N m c x) ((hairC G e E).buy Z*B):=by
    let V:=Canopy.pageS G (e+1) E; let C:=V.buy Z; obtain ⟨h1,h2⟩:= g.direction_cost p (FitS.X (e:=e)) (by omega); rw [mul_one] at h1 h2; let aim v:=insertQ v* (PowerSeries.X:InkQ)
    have he (p:Cost)(u':FitS e (Bank.reel p PowerSeries.X) C):FitsZ e (flyQ p x) ((hairC G e E).buy Z*B):=by
        have hx: aim p=insertQ (Bank.reel p PowerSeries.X):=by unfold aim; rw [reel_X,map_mul, map_X]
        have hv:FitsZ e (aim p) C:=by rw [hx]; exact FitsZ.written u'
        apply (retape hv u (V.purchase g.positive) (by unfold aim; simp)).lift; unfold hairC; rw [Credit.products, Credit.power, Credit.products]; change _≤ ((↑(e+1)*Z^0)* (((↑(e+1)*Z^0)*C)^e))*B; ring_nf; push_cast; ring_nf; exact le_rfl -- simparith
    exact ⟨he _ h1,he _ h2⟩
end FitsZ
end YM.WilsonCoeffUV.Mer.Xa
