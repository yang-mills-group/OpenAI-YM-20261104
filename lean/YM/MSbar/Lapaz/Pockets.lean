import YM.MSbar.Lapaz.Bruise
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lapaz
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Kelvin Further.GaussianScalar
variable {ι σ: Type} [Fintype σ][DecidableEq σ] [Fintype ι][DecidableEq ι]
variable (P:Matrix ι σ ℝ){C:Matrix σ σ ℝ} (hc:C.PosDef) {L x y a b u c r D:ℝ}
local notation "V"=> View σ
local notation "M"=> fieldLaw C
variable (h:∀ i:σ, C i i≤c) {n p:ℕ}
variable (Q S:SpringK ι)(X:View ι){p:ℕ}(hQ:Kind Q)
local notation "Q₀"=> Rewind Q X
local notation "Ψ"=> micro X P
local notation "Ω"=> Spring
local notation "T!"=>P*C*P.transpose
local notation "E!"=>picture X
local notation "I!"=> vow P C Q X
local notation "o!"=> owes P C Q S X p
local notation "k"=>PowerSeries.coeff
variable {A B t R W d r1 r2:ℝ}{Z: Set (View σ)}{s:ℕ}
variable (hS:∀ x:View σ, Belt p (micro X P (Rewind Q X) x)≤A*(1+‖x‖)^s ∧ Belt p (micro X P S x) ≤ B*(1+‖x‖)^s)
include hS hQ
local notation "F"=> micro X P (Rewind Q X)
local notation "f"=> micro X P S
include hc h
local notation "z1"=> fish (Fintype.card σ) (s*p) c (bag p A) L R
local notation "z2"=> fish (Fintype.card σ) (s+s*p) c (B*bag p A) L R
local notation "r1'"=>fish (Fintype.card σ) 0 c d L R
local notation "r2'"=>fish (Fintype.card σ) s c (d*B) L R
noncomputable def cloudK (i:ℕ)(p:ℕ)(s:ℕ)(c A:ℝ):= (((p+1:ℕ):ℝ))* (bag p A * boreo i c (s*p))
noncomputable def cloudL (i:ℕ)(p s:ℕ) (c A B:ℝ):= division (((p+1:ℕ):ℝ)*(B*bag p A*boreo i c (s+s*p))) (cloudK i p s c A) p
local notation "i!"=>cloudK (Fintype.card σ) p s c A
local notation "j!"=>cloudL (Fintype.card σ) p s c A B
local notation "χ!"=>boreo (Fintype.card σ)
lemma honor : Belt p (vow P C Q X)≤ i!∧ Belt p (owes P C Q S X p) ≤ j! :=by
    have hA:0≤ A:=by have hp:=(Belt_pos p _).trans (hS 0|>.1); simpa using hp
    have hB:0≤ B:=by have hp:=(Belt_pos p _).trans (hS 0|>.2); simpa using hp
    have hs:0≤ bag p A:=by unfold bag; exact Finset.sum_nonneg fun i _=> mul_nonneg (by positivity) (pow_nonneg hA _)
    let O := owes P C Q S X p; let I:= vow P C Q X
    have hh(i:ℕ)(hi:i≤p) : |k i I|≤ bag p A*χ! c (s*p)∧ |k i (O*I)|≤ B*bag p A*χ! c (s+s*p):=by
        unfold I O; rw [← edible P hc Q X hQ i,← firm P hc Q S X hQ i hi]; constructor
        · exact spread hc h _ (by simp_rw [Lapaz.sin]; exact pic ..) (fun x=> (Belt_entry _ p i hi).trans (winds P Q S X hQ hS x|>.1)) hs|>.2 -- hi proof needs
        exact spread hc h _ (by simp_rw [Lapaz.pervades P hc]; exact pic ..) (fun x=>(Belt_entry _ p i hi).trans (winds P Q S X hQ hS x|>.2)) (mul_nonneg hB hs)|>.2
    let D:= (p+1:ℕ)*(B*bag p A*χ! c (s+s*p)); have hx:Belt p I≤ i! := (sum_le_sum fun i hi=> hh i (Nat.lt_succ_iff.mp (mem_range.mp hi))|>.1).trans_eq (by unfold cloudK;rw [sum_const,nsmul_eq_mul,card_range]); have hy: Belt p (O*I) ≤ D:=(sum_le_sum fun i hi=> hh i (Nat.lt_succ_iff.mp (mem_range.mp hi))|>.2).trans_eq (by unfold D;rw [sum_const,nsmul_eq_mul,card_range]); have ht : k 0 I=1:=by unfold I vow picture; rw [PowerSeries.coeff_map,Cacao.covers, map_one]; exact sugar _ (hush hQ)
    refine ⟨hx,(divisionP I O ht hy hx).trans ?_⟩; unfold cloudL division; have hp:0 ≤ D:=(Belt_pos ..).trans hy; have hX:0 ≤ cloudK (Fintype.card σ) p s c A:=(Belt_pos ..).trans hx; change _ ≤ ((↑(p+1)+1)*D*(1+p*i!)^p); gcongr; linarith
variable (D': View σ→ℝ)(hr:Measurable D')(hd:∀ i,|D' i| ≤ d)
include hr hd
local notation "u!"=>d*B*boreo (Fintype.card σ) c s+d*j!
noncomputable def cov (T:View σ→ℝ) (p:ℕ) := (∫ i,T i*k 0 (micro X P S i)∂M)-(∫ i,T i∂M)*k 0 (owes P C Q S X p)
lemma tax : |cov P Q S X (C:=C) D' p|≤ u! :=by
    have hx:= (embers P hc h Q S X hQ hS D' hr hd); have ht:0≤ d:=(abs_nonneg _).trans (hd 0); apply (abs_sub ..).trans; apply add_le_add hx.2.2.2; rw [abs_mul]; exact mul_le_mul hx.2.2.1 ((Belt_entry _ p 0 (Nat.zero_le _)).trans (honor P hc h Q S X hQ hS|>.2)) (abs_nonneg _) ht
variable (hz:MeasurableSet Z) (hμ:(fieldLaw C).real Zᶜ ≤ R)(hy:0<L)(ht :0≤ t)(hp :t≤ 1)
include hz hμ hy ht hp
-- costs locality ratio charge.
variable (g h':View σ→ℝ)
local notation "P0"=> purse Z g
lemma quilt (he:Integrable (purse Z g) (fieldLaw C))(h1: Integrable ((purse Z g)*h') (fieldLaw C)) (h2:Measurable h')(hv: t*r1 ≤ r) (hits:∀ x:View σ,x∈Z → Belt p (micro X P (Rewind Q X) x)≤r1∧ Belt p (micro X P S x)≤ r2)
    (hm: ∀ x: View σ, x∈Z→|g x-taste p (micro X P (Rewind Q X) x) t-D' x|≤ a ∧ |h' x- taste p (micro X P S x) t| ≤ b):
    Survey (fieldLaw C) Z (micro X P (Rewind Q X)) (micro X P S) h' g D' p t (z2+r2') (z1+r1') d r2 a r r1 b :=by
     obtain ⟨hx,hH,-⟩:= embers P hc h Q S X hQ hS D' hr hd
     have hy:= Lapaz.trace P hc h Q S X hQ hS D' hr hd hz.compl hμ hy ht hp
     refine ⟨hz,he,h1,fun v=> (earth P hc h Q S X hQ hS v).1,fun v=>earth P hc h Q S X hQ hS v|>.2,fun v=>?_,ht,hp,hv,hits,h2,hx,hH,fun i hi=>⟨hd i,hm i hi⟩,hy.1,hy.2⟩
     unfold Kind micro picture; rw [PowerSeries.coeff_map,hush hQ,map_zero]
local notation "a0"=> deltaC a d r1 0 0 r t p
local notation "a1"=> debit p r1 r d a t b a0 r2
local notation "aZ"=> deltaC a d r1 0 0 r t p+(z1+r1')
noncomputable def expBill (p s m:ℕ)(L c t A B d a b r u v w:ℝ):=
     let x:=cloudK m p s c A; let y:=cloudL m p s c A B
     let δ:= deltaC a d u 0 0 r t p
     let D:= δ+(fish m (s*p) c (bag p A) L w + fish m 0 c d L w);
     let p':= debit p u r d a t b δ v+(fish m (s+s*p) c (B*bag p A) L w+fish m s c (d*B) L w)
     2*Survey.fee p t y x d D p' y (d*B*boreo m c s+d*y) (t*x+d+D)
lemma outfits (H:Survey (fieldLaw C) Z (micro X P (Rewind Q X)) (micro X P S) h' g D' p t (z2+r2') (z1+r1') d r2 a r r1 b)(he: Z.Nonempty)(hc' :t* i!+d +aZ ≤1/2) :
    |(∫ i:View σ,P0 i*h' i∂fieldLaw C)/(∫ i:View σ,P0 i∂fieldLaw C)- (taste p (owes P C Q S X p) t+cov P Q S X (C:=C) D' p)| ≤ expBill p s (Fintype.card σ) L c t A B d a b r r1 r2 R:=by
     obtain ⟨hx,hv⟩:= honor P hc h Q S X hQ hS; have hD:=embers P hc h Q S X hQ hS D' hr hd; have ht':=(tax P hc h Q S X hQ hS D' hr hd)
     unfold cov owes picture at ht'; rw [PowerSeries.coeff_map] at ht' -- rewrite first? cov O.S.X
     exact cubed X P Q S X hc hQ p H he hx hv hD.2.2.1 ht' hc'|>.2
end YM.MSbar.Lapaz
